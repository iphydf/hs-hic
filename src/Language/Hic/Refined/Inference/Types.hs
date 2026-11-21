{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
module Language.Hic.Refined.Inference.Types
    ( RefinedResult (..)
    , TaggedUnionInfo (..)
    , TranslatorState (..)
    , emptyTranslatorState
    , addConstraint
    , addConstraintCoerced
    , addCastConstraint
    , addNode
    , addInherit
    , TargetKind (..)
    , addFunction
    , addVar
    , addTaggedUnion
    , isNumber
    , isNumeric
    , isReference
    , lookThroughTargets
    ) where

import           Control.Applicative                  ((<|>))
import           Data.Aeson                           (ToJSON (..), object,
                                                       (.=))
import           Data.Map.Strict                      (Map)
import qualified Data.Map.Strict                      as Map
import           Data.Maybe                           (mapMaybe)
import qualified Data.Set                             as Set
import           Data.Text                            (Text)
import qualified Data.Text                            as T
import           Data.Word                            (Word32)
import           GHC.Generics                         (Generic)

import           Language.Cimple                      (Lexeme (..))
import           Language.Hic.Core.Errors
import           Language.Hic.Refined.Context
import           Language.Hic.Refined.LatticeOp
import           Language.Hic.Refined.PathContext
import           Language.Hic.Refined.Registry
import           Language.Hic.Refined.Solver          (Constraint (..))
import           Language.Hic.Refined.State
import           Language.Hic.Refined.Transition
import           Language.Hic.Refined.Types
import qualified Language.Hic.TypeSystem.Core.Base    as TS

import           Language.Hic.Refined.Inference.Utils

data RefinedResult = RefinedResult
    { rrHotspots        :: [Text]
    , rrSolverStates    :: Map Word32 (AnyRigidNodeF TemplateId Word32)
    , rrRegistry        :: Registry Word32
    , rrSolved          :: Either ProductState MappingRefinements
    , rrSolverSteps     :: Int
    -- ^ How many product states the solver processed.
    , rrStepsByOrigin   :: Map (Maybe FilePath, Int) Int
    -- ^ Solver steps by the source line (file, line) of their constraint.
    , rrNodesByFunction :: Map (FilePath, Text) Int
    -- ^ Type nodes made while collecting each function.
    , rrFunctionStarts  :: Map FilePath (Map Int Text)
    -- ^ The line each function starts on.
    , rrErrors          :: [ErrorInfo 'TS.Global]
    } deriving (Show)

instance ToJSON RefinedResult where
    toJSON RefinedResult{..} = object [ "hotspots" .= rrHotspots, "solved" .= rrSolved, "errors" .= rrErrors ]

data TaggedUnionInfo = TaggedUnionInfo
    { tuiTagField   :: Text
    , tuiUnionField :: Text
    , tuiMembers    :: Map Text Text -- ^ EnumVal -> MemberName
    } deriving (Show)

-- | What kind of constraint links a node to a target in 'tsTargets'.
data TargetKind = MeetTarget | InheritTarget
    deriving (Show, Eq)

-- | State for the refinement translator.
data TranslatorState = TranslatorState
    { tsNextId          :: Word32
    , tsNodes           :: Map Word32 (AnyRigidNodeF TemplateId Word32)
    , tsVarNodes        :: Map TemplateId Word32
    -- ^ The newest node of each type variable in 'tsNodes'.
    , tsCache           :: Map (TS.TypeInfo 'TS.Global) Word32
    , tsConstraints     :: [Constraint]
    , tsTargets         :: Map Word32 [(TargetKind, Word32)]
    -- ^ For each node, the nodes its constraints point at, newest first.
    , tsCurrentPath     :: SymbolicPath
    , tsCurrentFile     :: FilePath
    , tsVars            :: Map Text Word32
    , tsFunctions       :: Map Text Word32
    , tsTypeSystem      :: TS.TypeSystem
    , tsTaggedUnions    :: Map Text TaggedUnionInfo
    , tsArrayInstances  :: Map (Word32, Integer) Word32
    , tsExistentials    :: Map Text Word32
    , tsCurrentReturn   :: Maybe Word32
    , tsErrors          :: [ErrorInfo 'TS.Global]
    , tsSubstCache      :: Map Word32 Word32
    , tsFieldInstances  :: Map (Word32, Text) Word32
    -- ^ The instance of each struct-pointer field read from each instance.
    , tsStructCalls     :: [(Text, Text, Int, Text)]
    -- ^ Calls a struct's own data is passed to, like @p->cb(p->userdata)@:
    -- (struct, callback field, argument index, data field). They hold for
    -- every instance of the struct.
    , tsStructInstances :: Map Text (Map Word32 (Maybe (Map TemplateId Word32)))
    -- ^ Each struct's accessed instances: through a pointer (its parameters are
    -- skolems of the instance), or by value with its parameters' nodes.
    , tsAccessedFields  :: Set.Set (Word32, Text)
    -- ^ The fields read from each struct instance.
    , tsMemberTypes     :: Map (Word32, Text, [Word32], Text) Word32
    -- ^ The type of each field read from each instance: see 'memberOf'.
    , tsUnpacked        :: Map (Word32, Word32) Word32
    -- ^ Each existential body unpacked for each instance.
    , tsSkolems         :: Map (Word32, TemplateId) Word32
    -- ^ The node of each struct parameter of each instance read through a pointer.
    , tsCurrentFunction :: Text
    -- ^ The function being collected, for 'tsNodesByFunction'.
    , tsFunctionLoc     :: Maybe (Lexeme Text)
    -- ^ Where that function is, for constraints made without a location.
    , tsNodesByFunction :: Map (FilePath, Text) Int
    -- ^ How many type nodes each function's collection made (a cost report).
    , tsFunctionStarts  :: Map FilePath (Map Int Text)
    -- ^ The line each function starts on, to name the function of a source line.
    , tsOwnParams       :: Map Text [Bool]
    -- ^ Which of each struct's parameters in the type system are its own.
    , tsCasts           :: Set.Set (Word32, Word32)
    -- ^ The constraints casts make, (cast type, expression): a conflict they
    -- lead to is reported as a cast's.
    , tsDefinitions     :: Map Word32 Word32
    -- ^ Each variable made for a declaration ('refreshInstance'), with the
    -- type it's declared with.
    }

-- Helper functions for record updates to assist GHC type inference
addConstraint :: Maybe (Lexeme Text) -> PathContext -> Word32 -> Word32 -> TranslatorState -> TranslatorState
addConstraint loc ctx l r s = dtrace ("addConstraint: " ++ show l ++ " <: " ++ show r) $ s
    { tsConstraints = CSubtype l r PMeet emptyContext ctx 0 0 (loc <|> tsFunctionLoc s) (tsCurrentFile s) : tsConstraints s
    , tsTargets = Map.insertWith (++) l [(MeetTarget, r)] (tsTargets s)
    }

-- | One-way inheritance: @l@ takes what's known about @r@.
addInherit :: Maybe (Lexeme Text) -> Word32 -> Word32 -> TranslatorState -> TranslatorState
addInherit loc l r s = s
    { tsConstraints = CInherit l r (loc <|> tsFunctionLoc s) (tsCurrentFile s) : tsConstraints s
    , tsTargets = Map.insertWith (++) l [(InheritTarget, r)] (tsTargets s)
    }

isNumeric :: Maybe (AnyRigidNodeF TemplateId Word32) -> Bool
isNumeric = \case
    Just (AnyRigidNodeF (RObject s _)) ->
        case s of
            VBuiltin bt     -> bt /= NullPtrTy
            VSingleton bt _ -> bt /= NullPtrTy
            VEnum _         -> True
            VNominal (L _ _ (TIdName name)) _ ->
                name `elem` [ "int", "long", "short", "char"
                            , "int8_t", "uint8_t", "int16_t", "uint16_t"
                            , "int32_t", "uint32_t", "int64_t", "uint64_t"
                            , "size_t", "ssize_t", "uintptr_t", "intptr_t"
                            , "off_t", "bool"
                            ]
            _ -> False
    _ -> False

-- | Whether a node is a number: a numeric type, or an enum's type. Copying
-- one into another isn't checked here: what fits is tokstyle's to check.
isNumber :: TS.TypeSystem -> Maybe (AnyRigidNodeF TemplateId Word32) -> Bool
isNumber ts node = isNumeric node || case node of
    Just (AnyRigidNodeF (RObject (VNominal (L _ _ (TIdName name)) _) _)) -> case TS.lookupType name ts of
        Just TS.EnumDescr{} -> True
        Just TS.IntDescr{}  -> True
        _                   -> False
    _ -> False

isReference :: Maybe (AnyRigidNodeF TemplateId Word32) -> Bool
isReference = \case
    Just (AnyRigidNodeF (RReference _ _ _ _)) -> True
    _ -> False

-- | A value flowing from @l0@ into @r@: assigned, returned, passed or
-- initialised. What flows is a copy, which doesn't keep the source's own
-- qualifiers (as in C's value conversion): a constant struct can be copied into
-- mutable storage. What a copied pointer points to keeps its own.
addConstraintCoerced :: Maybe (Lexeme Text) -> PathContext -> Word32 -> Word32 -> TranslatorState -> TranslatorState
addConstraintCoerced loc ctx l r = snd . valueFlow loc ctx l r

-- | A cast's value flow ('addConstraintCoerced'), recorded as a cast's.
addCastConstraint :: Maybe (Lexeme Text) -> PathContext -> Word32 -> Word32 -> TranslatorState -> TranslatorState
addCastConstraint loc ctx l r s = case valueFlow loc ctx l r s of
    (Just c, s')  -> s' { tsCasts = Set.insert c (tsCasts s') }
    (Nothing, s') -> s'

-- | What a variable stands for: its declared type if it was declared (declared
-- variables go by their declaration), else what it's constrained to, newest
-- first.
lookThroughTargets :: TranslatorState -> Word32 -> [(TargetKind, Word32)]
lookThroughTargets s nid = case Map.lookup nid (tsDefinitions s) of
    Just ty -> [(MeetTarget, ty)]
    Nothing -> Map.findWithDefault [] nid (tsTargets s)

-- | A value flow, and the (left, right) of the constraint it makes, if any:
-- numbers flow into each other unchecked.
valueFlow :: Maybe (Lexeme Text) -> PathContext -> Word32 -> Word32 -> TranslatorState -> (Maybe (Word32, Word32), TranslatorState)
valueFlow loc ctx l0 r s0 =
    let unqualified = Quals False False
        copy node =
            let nid = tsNextId s0
            in (nid, addNode nid node s0 { tsNextId = nid + 1 })
        (l, s) = case Map.lookup l0 (tsNodes s0) of
            Just (AnyRigidNodeF (RObject o q)) | q /= unqualified          -> copy (AnyRigidNodeF (RObject o unqualified))
            Just (AnyRigidNodeF (RReference ref n o q)) | q /= unqualified -> copy (AnyRigidNodeF (RReference ref n o unqualified))
            _                                                              -> (l0, s0)
        -- Variables can be constrained to each other in a cycle (e.g. @p = p + 1@),
        -- so skip constraints back to a variable we've already seen.
        lookThrough :: Set.Set Word32 -> Word32 -> Word32
        lookThrough visited nid = case Map.lookup nid (tsNodes s) of
            Just (AnyRigidNodeF (RObject (VVar _tid _) _)) ->
                let visited' = Set.insert nid visited
                in case filter (`Set.notMember` visited') (map snd (lookThroughTargets s nid)) of
                    (targetId:_) -> lookThrough visited' targetId
                    []           -> nid
            _ -> nid
        idL = lookThrough Set.empty l
        idR = lookThrough Set.empty r
        nodeL = Map.lookup idL (tsNodes s)
        nodeR = Map.lookup idR (tsNodes s)
    in if isNumber (tsTypeSystem s) nodeL && isNumber (tsTypeSystem s) nodeR
       then (Nothing, s)
       else (Just (l, r), addConstraint loc ctx l r s)

addNode :: Word32 -> AnyRigidNodeF TemplateId Word32 -> TranslatorState -> TranslatorState
addNode nid node s = s
    { tsNodes = Map.insert nid node (tsNodes s)
    , tsNodesByFunction = Map.insertWith (+) (tsCurrentFile s, tsCurrentFunction s) 1 (tsNodesByFunction s)
    , tsVarNodes = case node of
        AnyRigidNodeF (RObject (VVar tid _) _) -> Map.insertWith max tid nid (tsVarNodes s)
        _                                      -> tsVarNodes s
    }

addFunction :: Text -> Word32 -> TranslatorState -> TranslatorState
addFunction name nid s = s { tsFunctions = Map.insert name nid (tsFunctions s) }

addVar :: Text -> Word32 -> TranslatorState -> TranslatorState
addVar name nid s = s { tsVars = Map.insert name nid (tsVars s) }

addTaggedUnion :: Text -> TaggedUnionInfo -> TranslatorState -> TranslatorState
addTaggedUnion name tu s = s { tsTaggedUnions = Map.insert name tu (tsTaggedUnions s) }

emptyTranslatorState :: TS.TypeSystem -> TranslatorState
emptyTranslatorState ts = TranslatorState
    { tsNextId = 3
    , tsNodes  = Map.fromList
        [ (0, AnyRigidNodeF (RTerminal SBottom))
        , (1, AnyRigidNodeF (RTerminal SAny))
        , (2, AnyRigidNodeF (RTerminal SConflict))
        ]
    , tsVarNodes = Map.empty
    , tsCache  = Map.empty
    , tsConstraints = []
    , tsTargets = Map.empty
    , tsCurrentPath = emptyPath
    , tsCurrentFile = ""
    , tsVars = Map.empty
    , tsFunctions = Map.empty
    , tsTypeSystem = ts
    , tsTaggedUnions = Map.empty
    , tsArrayInstances = Map.empty
    , tsExistentials   = Map.empty
    , tsCurrentReturn  = Nothing
    , tsErrors = []
    , tsSubstCache = Map.empty
    , tsFieldInstances = Map.empty
    , tsStructCalls = []
    , tsStructInstances = Map.empty
    , tsAccessedFields = Set.empty
    , tsMemberTypes = Map.empty
    , tsUnpacked = Map.empty
    , tsSkolems = Map.empty
    , tsCurrentFunction = "<top level>"
    , tsFunctionLoc = Nothing
    , tsNodesByFunction = Map.empty
    , tsFunctionStarts = Map.empty
    , tsOwnParams = Map.empty
    , tsCasts = Set.empty
    , tsDefinitions = Map.empty
    }
