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
    , addNode
    , addFunction
    , addVar
    , addTaggedUnion
    , isNumeric
    , isReference
    ) where

import           Data.Aeson                           (ToJSON (..), object,
                                                       (.=))
import           Data.Map.Strict                      (Map)
import qualified Data.Map.Strict                      as Map
import           Data.Maybe                           (mapMaybe)
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
    { rrHotspots     :: [Text]
    , rrSolverStates :: Map Word32 (AnyRigidNodeF TemplateId Word32)
    , rrRegistry     :: Registry Word32
    , rrSolved       :: Either ProductState MappingRefinements
    , rrErrors       :: [ErrorInfo 'TS.Global]
    } deriving (Show)

instance ToJSON RefinedResult where
    toJSON RefinedResult{..} = object [ "hotspots" .= rrHotspots, "solved" .= rrSolved, "errors" .= rrErrors ]

data TaggedUnionInfo = TaggedUnionInfo
    { tuiTagField   :: Text
    , tuiUnionField :: Text
    , tuiMembers    :: Map Text Text -- ^ EnumVal -> MemberName
    } deriving (Show)

-- | State for the refinement translator.
data TranslatorState = TranslatorState
    { tsNextId         :: Word32
    , tsNodes          :: Map Word32 (AnyRigidNodeF TemplateId Word32)
    , tsCache          :: Map (TS.TypeInfo 'TS.Global) Word32
    , tsConstraints    :: [Constraint]
    , tsCurrentPath    :: SymbolicPath
    , tsCurrentFile    :: FilePath
    , tsVars           :: Map Text Word32
    , tsFunctions      :: Map Text Word32
    , tsTypeSystem     :: TS.TypeSystem
    , tsTaggedUnions   :: Map Text TaggedUnionInfo
    , tsArrayInstances :: Map (Word32, Integer) Word32
    , tsExistentials   :: Map Text Word32
    , tsCurrentReturn  :: Maybe Word32
    , tsErrors         :: [ErrorInfo 'TS.Global]
    , tsSubstCache     :: Map Word32 Word32
    }

-- Helper functions for record updates to assist GHC type inference
addConstraint :: Maybe (Lexeme Text) -> PathContext -> Word32 -> Word32 -> TranslatorState -> TranslatorState
addConstraint loc ctx l r s = dtrace ("addConstraint: " ++ show l ++ " <: " ++ show r) $ s { tsConstraints = CSubtype l r PMeet emptyContext ctx 0 0 loc (tsCurrentFile s) : tsConstraints s }

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

isReference :: Maybe (AnyRigidNodeF TemplateId Word32) -> Bool
isReference = \case
    Just (AnyRigidNodeF (RReference _ _ _ _)) -> True
    _ -> False

addConstraintCoerced :: Maybe (Lexeme Text) -> PathContext -> Word32 -> Word32 -> TranslatorState -> TranslatorState
addConstraintCoerced loc ctx l r s =
    let lookThrough nid = case Map.lookup nid (tsNodes s) of
            Just (AnyRigidNodeF (RObject (VVar _tid _) _)) ->
                let isTarget = \case
                        CSubtype l' r' PMeet _ _ _ _ _ _ | l' == nid -> Just r'
                        CInherit l' r' _ _ | l' == nid -> Just r'
                        _ -> Nothing
                in case mapMaybe isTarget (tsConstraints s) of
                    (targetId:_) -> lookThrough targetId
                    []           -> nid
            _ -> nid
        idL = lookThrough l
        idR = lookThrough r
        nodeL = Map.lookup idL (tsNodes s)
        nodeR = Map.lookup idR (tsNodes s)
    in if isNumeric nodeL && isNumeric nodeR
       then s
       else addConstraint loc ctx l r s


addNode :: Word32 -> AnyRigidNodeF TemplateId Word32 -> TranslatorState -> TranslatorState
addNode nid node s = s { tsNodes = Map.insert nid node (tsNodes s) }

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
    , tsCache  = Map.empty
    , tsConstraints = []
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
    }
