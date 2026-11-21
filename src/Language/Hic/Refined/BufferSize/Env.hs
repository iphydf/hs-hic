{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

-- | What every function can see: constants, types, signatures and
-- globals.
module Language.Hic.Refined.BufferSize.Env
    ( CType (..)
    , unknownType
    , Param (..)
    , Signature (..)
    , Env (..)
    , FieldPair (..)
    , ParamPlace (..)
    , ConstDef (..)
    , ConstKind (..)
    , collectEnv
    , constDefs
    , allocSizesOf
    , aggregatesOf
    , aliasesOf
    , typeSize
    , dimOf
    , constRange
    , builtinSize
    , pointerSize
    , integerType
    , isIntegerType
    , typeOfDecl
    , declType
    , declTypeWith
    , typeBytes
    , isBufferType
    , isByteType
    , envConstRange
    , envNamedSize
    , typedefsOf
    , structsOf
    , pairsOf
    , globalsOf
    , mutableGlobalsOf
    , isConstType
    , signaturesOf
    , paramsOf
    , resolveType
    , isPointerType
    , typeOfExpr
    , localsOf
    , subnodes
    , zeroInitialiser
    , isNullptr
    ) where

import           Control.Applicative                      ((<|>))
import           Data.Fix                                 (Fix (..), unFix)
import           Data.Foldable                            (toList)
import           Data.Map.Strict                          (Map)
import qualified Data.Map.Strict                          as Map
import           Data.Maybe                               (fromMaybe, isJust,
                                                           listToMaybe)
import qualified Data.Set                                 as Set
import           Data.Text                                (Text)
import qualified Data.Text                                as T
import           Language.Cimple                          (Lexeme (..),
                                                           NodeF (..))
import qualified Language.Cimple                          as C
import           Language.Hic.Refined.BufferSize.Facts    (Lin)
import           Language.Hic.Refined.BufferSize.Integers
import           Language.Hic.Refined.BufferSize.Paths    (Step)
import qualified Language.Hic.Refined.Inference.Platform  as Platform

-- | A place a function is given: a parameter, by position, or a place
-- fields and pointers lead to from one, and elements at parameters (an
-- index named @#k@).
data ParamPlace = ParamPlace Int [Step]
    deriving (Show, Eq, Ord)

-- | A C type as far as sizes go: the name it's built from, how many pointers
-- deep it is, and its array dimensions (outermost first).
data CType = CType
    { ctName     :: Text
    , ctPointers :: Int
    , ctDims     :: [Range]
    }
    deriving (Show, Eq)

unknownType :: CType
unknownType = CType "" 0 []

data Param = Param
    { paramType      :: CType
    , paramLength    :: Maybe Int
      -- ^ The position of the integer parameter after it that says how long
      -- it is.
    , paramOutLength :: Maybe Int
      -- ^ For an out-parameter for a buffer, the position of the one after
      -- it for its length.
    }

data Signature = Signature
    { sigReturn :: CType
    , sigParams :: [Maybe Param]
      -- ^ One per argument; 'Nothing' for @...@.
    }

-- | What every function can see: constants, types and signatures.
data Env = Env
    { envConstants    :: Map Text Range
    , envConstTypes   :: Map Text IntType
    , envTypeSizes    :: Map Text Range
      -- ^ Sizes of structs, unions and typedefs.
    , envStructs      :: Map Text (Map Text CType)
    , envFieldOrder   :: Map Text [Text]
      -- ^ The fields of each struct, in the order they're declared, where
      -- that's all its members are.
    , envTypedefs     :: Map Text CType
    , envFunctions    :: Map Text Signature
      -- ^ Functions, and function typedefs for calls through pointers.
    , envGlobals      :: Map Text CType
    , envMutable      :: Set.Set Text
      -- ^ Global variables that aren't const.
    , envReturns      :: Map Text Integer
      -- ^ How many elements a function's result has at least.
    , envIntReturns   :: Map Text Range
      -- ^ Bounds of what a function returning an integer returns.
    , envAtMost       :: Map Text (Map Int Integer)
      -- ^ Integer parameters (by position) a function returning an integer
      -- returns at most so much more than, unless it returns less than 0.
    , envBelow        :: Map Text Int
      -- ^ A function returning an unsigned integer that returns less than a
      -- parameter (by position) where it's at least 1, else 0.
    , envAtMostUnless :: Map Text (Integer, Map Int Integer)
      -- ^ The same of a function returning an unsigned integer, unless it
      -- returns the most its type holds: what it returns for none.
    , envTrue         :: Map Text (Map Int Range)
      -- ^ What a function returning @bool@ has made sure of its integer
      -- parameters (by position) where it returns true.
    , envMadeSums     :: Map Text [(Map ParamPlace Integer, Integer)]
      -- ^ Sums of what a function is given, and of what fields and pointers
      -- lead to from it, known to be at least a bound where it says it did
      -- what it was asked: returns true, or 0.
    , envReturnsPlace :: Map Text ParamPlace
      -- ^ What a function returning a pointer returns the address of where
      -- it doesn't return nullptr.
    , envAtMostPlaces :: Map Text (Map ParamPlace Integer)
      -- ^ Integer places fields and pointers lead to from the pointer
      -- parameters of a function returning an integer, which it returns at
      -- most so much more than, whatever it returns.
    , envMadeSizes    :: Map Text (Map ParamPlace Lin)
      -- ^ Buffers fields and pointers lead to from the pointer parameters
      -- of a function, and how many elements it has made each have (a sum
      -- of its integer parameters, @#k@) where it says it did: returns
      -- true, or 0.
    , envRelations    :: Map Text [Lin]
      -- ^ Sums of a function's integer parameters (@#k@ for the one at k
      -- from 0) its callers must make at least 0.
    , envFailures     :: Map Text [Range]
      -- ^ What a function returns below 0, for one that otherwise returns a
      -- number of at least 0 converted to its type.
    , envAllocSizes   :: Map Text [Int]
    , envZeroed       :: Set.Set Text
      -- ^ Functions that give back memory all zeros, where it isn't nullptr.
    , envZeroConsts   :: Set.Set Text
      -- ^ Constants that are all zeros, which structs are set to.
      -- ^ Functions returning allocated memory (@GNU_ALLOC_SIZE@): the
      -- arguments (from 1) whose product is its size in bytes.
    , envRequires     :: Map Text (Map Int Range)
      -- ^ What a function needs of its integer parameters (by position),
      -- checked at every call.
    , envPointsAtMost :: Map Text (Map Int Integer)
      -- ^ The most what a function's pointers to integers (by position)
      -- may point to where it starts, checked at every call.
    , envFieldRanges  :: Map (Text, Text) Range
      -- ^ What an integer field (by struct and name) is ever given.
    , envFields       :: Map (Text, Text) Integer
      -- ^ How many elements a pointer field (struct, field) points to at
      -- least, from everything put in it.
    , envPairs        :: Map Text [FieldPair]
      -- ^ The buffer fields of each struct that have a length field.
    , envNeeds        :: Map Text (Map Int [Lin])
      -- ^ What a function needs of the buffers it's given (by position),
      -- from what it does with them: sums of its parameters (@#2@ for the
      -- third) each buffer has at least as many elements as.
    , envKeeps        :: Map Text (Set.Set Int)
      -- ^ For each function defined in the program, the pointer parameters
      -- (by position) it may keep past a call.
    , envClosed       :: Set.Set Text
      -- ^ Static functions every call to which is one the program makes in
      -- a function it defines.
    , envGiven        :: Map Text (Map Int Range)
      -- ^ What every call to one of those gives its integer parameters (by
      -- position).
    , envGivenSums    :: Map Text [(Map ParamPlace Integer, Integer)]
      -- ^ Sums of what every call to one of those gives it, known to be at
      -- least a bound.
    , envLeaves       :: Map Text (Map ParamPlace Range)
      -- ^ What a function leaves places fields and pointers lead to from
      -- its pointer parameters at, wherever it ends.
    , envMadeStores   :: Map Text (Map Int Range)
      -- ^ What the integers a function's pointers it only stores to (by
      -- position) point to are where it says it did what it was asked.
    , envStores       :: Map Text (Map Int (Range, Map Int Integer))
      -- ^ What a function may store through a pointer to an integer (by
      -- position) it does nothing else with but read through and compare
      -- with nullptr: the bounds of the values, and how much more than
      -- each integer parameter (by position) they are at most. After a
      -- call, what's there is one of those, or what was there before.
    }

-- | A buffer field and the field saying how many elements it has room
-- for. That's its capacity if it has one, and then its count is at most
-- that.
data FieldPair = FieldPair
    { fpBuffer :: Text
    , fpLength :: Text
    , fpCount  :: Maybe Text
    }

data ConstDef
    = ConstExpr ConstKind (C.Node (Lexeme Text))
    | ConstAfter (Maybe Text)
      -- ^ An enumerator without a value: 1 more than the one before, or 0.

-- | Where a constant's type comes from.
data ConstKind
    = Defined
      -- ^ A @#define@: its value's type.
    | Declared (C.Node (Lexeme Text))
      -- ^ A @const@ with a type.
    | Enumerated

collectEnv :: [C.Node (Lexeme Text)] -> Env
collectEnv nodes =
    let defs = Map.fromListWith (\_ old -> old) (concatMap constDefs nodes)
        aggregates = Map.fromListWith (\_ old -> old) (concatMap aggregatesOf nodes)
        aliases = Map.fromListWith (\_ old -> old) (concatMap aliasesOf nodes)
        -- Constants and type sizes need each other (an array field's size, a
        -- sizeof in a #define), so they're worked out together, to a depth.
        constR :: Int -> Text -> Range
        constR d name
            | d <= 0 = unknownRange
            | otherwise = case Map.lookup name defs of
                Just (ConstExpr _ e)          -> constRange (constR (d - 1)) (sizeR (d - 1)) (const unknownRange) e
                Just (ConstAfter Nothing)     -> exactly 0
                Just (ConstAfter (Just prev)) -> rangeArith C.BopPlus (constR (d - 1) prev) (exactly 1)
                Nothing                       -> unknownRange
        sizeR :: Int -> Text -> Range
        sizeR d = fst . layoutR d
        -- A type's size and alignment, laid out as C does on every
        -- platform: with the least sizes and alignments, and with the most.
        layoutR :: Int -> Text -> (Range, Range)
        layoutR d name
            | d <= 0 = (unknownRange, unknownRange)
            | Just r <- builtinSize name = (r, builtinAlign name)
            | Just (isUnion, members) <- Map.lookup name aggregates =
                let fields = [ fieldLayout (d - 1) ty dims | (ty, dims) <- members ]
                    bound end = do
                        fs <- traverse (\(size, align) -> (,) <$> end size <*> end align) fields
                        let align = maximum (1 : map snd fs)
                            size = if isUnion then maximum (0 : map fst fs)
                                   else foldl' (\off (sz, al) -> roundUp off al + sz) 0 fs
                        return (roundUp size align, align)
                    low = fromMaybe (0, 1) (bound (\r -> Just (fromMaybe 0 (rLow r))))
                    high = bound rHigh
                in (Range (Just (fst low)) (fst <$> high), Range (Just (snd low)) (snd <$> high))
            | Just (ty, dims) <- Map.lookup name aliases = fieldLayout (d - 1) ty dims
            | otherwise = (unknownRange, unknownRange)
        fieldLayout d ty dims =
            let ct = typeOfDecl ty
                (size, align) = if ctPointers ct > 0 then (pointerSize, pointerSize) else layoutR d (ctName ct)
                counts = map (dimOf (constRange (constR d) (sizeR d) (const unknownRange))) dims
            in (foldl' (rangeArith C.BopMul) size counts, align)
        roundUp x a = if a <= 1 then x else ((x + a - 1) `div` a) * a
        depth = 20
        -- What the program defines, else the limits of <stdint.h>.
        consts = Map.filter (/= unknownRange) (Map.mapWithKey (\name _ -> constR depth name) defs)
            `Map.union` Map.map snd limits
        sizes = Map.filter (/= unknownRange) (Map.fromList [ (name, sizeR depth name) | name <- Map.keys aggregates ++ Map.keys aliases ])
        env0 = Env
            { envConstants = consts
            , envConstTypes = Map.empty
            , envTypeSizes = sizes
            , envStructs = Map.empty
            , envFieldOrder = Map.empty
            , envTypedefs = Map.empty
            , envFunctions = Map.empty
            , envGlobals = Map.empty
            , envMutable = Set.empty
            , envReturns = Map.empty
            , envIntReturns = Map.empty
            , envAtMost = Map.empty
            , envAtMostUnless = Map.empty
            , envBelow = Map.empty
            , envFailures = Map.empty
            , envRelations = Map.empty
            , envTrue = Map.empty
            , envMadeSums = Map.empty
            , envAtMostPlaces = Map.empty
            , envMadeSizes = Map.empty
            , envReturnsPlace = Map.empty
            , envAllocSizes = Map.empty
            , envRequires = Map.empty
            , envZeroed = Set.empty
            , envZeroConsts = Set.empty
            , envPointsAtMost = Map.empty
            , envFieldRanges = Map.empty
            , envFields = Map.empty
            , envPairs = Map.empty
            , envKeeps = Map.empty
            , envNeeds = Map.empty
            , envClosed = Set.empty
            , envGiven = Map.empty
            , envGivenSums = Map.empty
            , envStores = Map.empty
            , envMadeStores = Map.empty
            , envLeaves = Map.empty
            }
        typedefs = Map.fromList (concatMap (typedefsOf env0) nodes)
        env1 = env0 { envTypedefs = typedefs }
        -- A #define's type is its value's, which may use other constants.
        constT :: Int -> Text -> Maybe IntType
        constT d name
            | d <= 0 = Nothing
            | otherwise = case Map.lookup name defs of
                Just (ConstExpr Defined e)       -> arithType (constLeaf (d - 1)) e
                Just (ConstExpr (Declared ty) _) -> integerType env1 (typeOfDecl ty)
                Just (ConstExpr Enumerated _)    -> Just intType
                Just ConstAfter{}                -> Just intType
                Nothing                          -> Nothing
        constLeaf d (Fix n) = case n of
            LiteralExpr C.ConstId (L _ _ c) -> constT d c
            VarExpr (L _ _ c)               -> constT d c
            CastExpr ty _                   -> integerType env1 (typeOfDecl ty)
            _                               -> Nothing
        structs = Map.fromListWith (\_ old -> old) (concatMap (structsOf env1) nodes)
        protos = Map.fromListWith (\_ old -> old) (concatMap (signaturesOf env1 False) nodes)
        defns = Map.fromListWith (\_ old -> old) (concatMap (signaturesOf env1 True) nodes)
        globals = Map.fromList (concatMap (globalsOf env1) nodes)
    in env1
        { envConstTypes = Map.mapMaybe id (Map.mapWithKey (\name _ -> constT depth name) defs)
            `Map.union` Map.map fst limits
        , envStructs = structs
        , envFieldOrder = Map.fromListWith (\_ old -> old) (concatMap fieldOrderOf nodes)
        , envPairs = Map.fromListWith (\_ old -> old) (concatMap (pairsOf env1) nodes)
        , envFunctions = Map.mapWithKey unpairSizes (Map.unions [protos, defns, builtinFunctions])
        , envGlobals = globals
        , envMutable = Set.fromList (concatMap mutableGlobalsOf nodes)
        , envAllocSizes = allocSizes
        , envZeroed = zeroedFunctions allocSizes nodes
        , envZeroConsts = Set.fromList (concatMap zeroConstsOf nodes)
        }
  where
    allocSizes = Map.fromList (concatMap allocSizesOf nodes) `Map.union` builtinAllocSizes
    -- What an allocator is given to resize isn't as long as the new size.
    unpairSizes name sig = case Map.lookup name allocSizes of
        Just positions -> sig { sigParams = map (fmap (unpair positions)) (sigParams sig) }
        Nothing        -> sig
    unpair positions param
        | maybe False ((`elem` positions) . (+ 1)) (paramLength param) = param { paramLength = Nothing }
        | otherwise = param

constDefs :: C.Node (Lexeme Text) -> [(Text, ConstDef)]
constDefs (Fix node) = case node of
    PreprocDefineConst (L _ _ name) e -> [(name, ConstExpr Defined e)]
    ConstDefn _ ty (L _ _ name) e
        | isConstType ty              -> [(name, ConstExpr (Declared ty) e)]
    EnumDecl _ ms _                   -> enumerators ms
    EnumConsts _ ms                   -> enumerators ms
    FunctionDefn{}                    -> []
    _                                 -> concatMap constDefs (toList node)
  where
    enumerators = go Nothing . concatMap enumeratorOf
    go _ [] = []
    go prev ((name, mValue):rest) =
        (name, maybe (ConstAfter prev) (ConstExpr Enumerated) mValue) : go (Just name) rest
    enumeratorOf (Fix n) = case n of
        Enumerator (L _ _ name) mValue -> [(name, mValue)]
        Commented _ e                  -> enumeratorOf e
        _                              -> []

-- | Functions declared to return allocated memory, and which arguments
-- give its size.
-- | Constants whose initialisers are all zeros.
zeroConstsOf :: C.Node (Lexeme Text) -> [Text]
zeroConstsOf (Fix node) = case node of
    ConstDefn _ _ (L _ _ name) e | zeroInitialiser e -> [name]
    FunctionDefn{}                                    -> []
    _                                                 -> concatMap zeroConstsOf (toList node)

-- | An initialiser of zeros.
zeroInitialiser :: C.Node (Lexeme Text) -> Bool
zeroInitialiser (Fix n) = case n of
    InitialiserList xs                 -> all zeroInitialiser xs
    LiteralExpr C.Int (L _ _ t)        -> parseIntLiteral t == Just 0
    LiteralExpr C.Bool (L _ _ "false") -> True
    _                                  -> isNullptr (Fix n)

-- | Functions that give back memory all zeros, or nullptr: the C
-- library's that do, and those returning what one of them gives, or what
-- an allocator gives once all it asked for is set to zeros, where it isn't
-- nullptr.
zeroedFunctions :: Map Text [Int] -> [C.Node (Lexeme Text)] -> Set.Set Text
zeroedFunctions allocSizes nodes = grow (Set.filter Platform.returnsZeros (Map.keysSet allocSizes))
  where
    defns = [ (name, stmts) | Fix (FunctionDefn _ (Fix (FunctionPrototype _ (L _ _ name) _)) (Fix (CompoundStmt stmts))) <- concatMap subnodes nodes ]
    grow known =
        let known' = known <> Set.fromList [ name | (name, stmts) <- defns, zeroes known stmts ]
        in if known' == known then known else grow known'
    zeroes known stmts =
        let indexed = zip [0 :: Int ..] stmts
            returns = [ (i, e) | (i, s) <- indexed, Fix (Return (Just e)) <- subnodes s ]
            -- Locals given what a call gives, never given anything else.
            given = Map.fromList [ (v, call) | Fix (VarDeclStmt (Fix (VarDecl _ (L _ _ v) [])) (Just rhs)) <- stmts, Just call <- [callOf rhs] ]
            assigned = [ v | Fix (AssignExpr (Fix (VarExpr (L _ _ v))) _ _) <- concatMap subnodes stmts ]
            -- Where a local is set to zeros: at the top, or where it's
            -- checked not to be nullptr.
            zeroedAt v = [ i | (i, s) <- indexed, wipes v s ]
            wipes v (Fix s) = case s of
                ExprStmt e -> isWipe v e
                IfStmt c (Fix (CompoundStmt body)) Nothing | notNull v c -> or [ isWipe v e | Fix (ExprStmt e) <- body ]
                _ -> False
            isWipe v (Fix e) = case e of
                FunctionCall (Fix (VarExpr (L _ _ "memset"))) [p, z, size] ->
                    isVar v p && isZero z && Just (C.removeSloc size) == (C.removeSloc <$> allocSize v)
                _ -> False
            allocSize v = do
                (f, args) <- Map.lookup v given
                [k] <- Map.lookup f allocSizes
                listToMaybe (drop (k - 1) args)
            ok (i, e) = case unFix (strip e) of
                LiteralExpr C.ConstId (L _ _ "nullptr") -> True
                FunctionCall (Fix (VarExpr (L _ _ f))) _ -> Set.member f known
                VarExpr (L _ _ v) | v `notElem` assigned ->
                    maybe False ((`Set.member` known) . fst) (Map.lookup v given) || any (< i) (zeroedAt v)
                _ -> False
        in not (null returns) && all ok returns
    callOf e = case unFix (strip e) of
        FunctionCall (Fix (VarExpr (L _ _ f))) args -> Just (f, args)
        _                                           -> Nothing
    strip e@(Fix n) = case n of
        ParenExpr x  -> strip x
        CastExpr _ x -> strip x
        _            -> e
    isVar v p = case unFix (strip p) of
        VarExpr (L _ _ w) -> w == v
        _                 -> False
    isZero (Fix z) = case z of
        LiteralExpr C.Int (L _ _ "0") -> True
        _                             -> False
    notNull v (Fix c) = case c of
        BinaryExpr a C.BopNe (Fix (LiteralExpr C.ConstId (L _ _ "nullptr"))) -> isVar v a
        _                                                                   -> False

allocSizesOf :: C.Node (Lexeme Text) -> [(Text, [Int])]
allocSizesOf (Fix node) = case node of
    AttrAllocSize ls decl ->
        [ (name, positions) | Just name <- [declName decl], Just positions <- [traverse position ls] ]
    FunctionDefn{} -> []
    _ -> concatMap allocSizesOf (toList node)
  where
    position (L _ _ t) = fromInteger <$> parseIntLiteral t
    declName (Fix n) = case n of
        FunctionDecl _ proto            -> declName proto
        TypedefFunction proto           -> declName proto
        FunctionPrototype _ (L _ _ f) _ -> Just f
        _                               -> Nothing

-- | Structs and unions, with each field's type and dimensions.
aggregatesOf :: C.Node (Lexeme Text) -> [(Text, (Bool, [(C.Node (Lexeme Text), [C.Node (Lexeme Text)])]))]
aggregatesOf (Fix node) = case node of
    Struct (L _ _ name) members -> [(name, (False, concatMap member members))]
    Union (L _ _ name) members  -> [(name, (True, concatMap member members))]
    FunctionDefn{}              -> []
    _                           -> concatMap aggregatesOf (toList node)
  where
    member (Fix m) = case m of
        MemberDecl (Fix (VarDecl ty _ dims)) _ -> [(ty, dims)]
        Commented _ d                          -> member d
        _                                      -> concatMap member (toList m)

-- | Typedefs that aren't the struct or union of the same name.
aliasesOf :: C.Node (Lexeme Text) -> [(Text, (C.Node (Lexeme Text), [C.Node (Lexeme Text)]))]
aliasesOf (Fix node) = case node of
    Typedef (Fix (Struct (L _ _ s) _)) (L _ _ name) _ | s == name -> []
    Typedef (Fix (Union (L _ _ s) _)) (L _ _ name) _ | s == name  -> []
    Typedef (Fix (Struct (L p c s) _)) name dims -> [(lexemeText name, (Fix (TyStruct (L p c s)), dims))]
    Typedef (Fix (Union (L p c s) _)) name dims -> [(lexemeText name, (Fix (TyUnion (L p c s)), dims))]
    Typedef ty (L _ _ name) dims -> [(name, (ty, dims))]
    FunctionDefn{} -> []
    _ -> concatMap aliasesOf (toList node)
  where
    lexemeText (L _ _ t) = t

-- | The size of a type with its dimensions, from the sizes of named types.
typeSize :: (C.Node (Lexeme Text) -> Range) -> (Text -> Range) -> C.Node (Lexeme Text) -> [C.Node (Lexeme Text)] -> Range
typeSize dimRange namedSize ty dims =
    let ct = typeOfDecl ty
        element = if ctPointers ct > 0 then pointerSize else namedSize (ctName ct)
    in foldl' (rangeArith C.BopMul) element (map (dimOf dimRange) dims)

dimOf :: (C.Node (Lexeme Text) -> Range) -> C.Node (Lexeme Text) -> Range
dimOf dimRange (Fix (DeclSpecArray _ (Just e))) = dimRange e
dimOf _ _                                       = unknownRange

-- | Bounds of a constant expression, from the bounds of other constants and
-- the sizes of named types.
constRange :: (Text -> Range) -> (Text -> Range) -> (C.Node (Lexeme Text) -> Range) -> C.Node (Lexeme Text) -> Range
constRange lookupConst namedSize sizeofExpr = go
  where
    go (Fix node) = case node of
        LiteralExpr C.Int (L _ _ t)     -> maybe unknownRange exactly (parseIntLiteral t)
        LiteralExpr C.ConstId (L _ _ t) -> lookupConst t
        VarExpr (L _ _ t)               -> lookupConst t
        ParenExpr e                     -> go e
        CastExpr _ e                    -> go e
        SizeofType ty                   -> typeSize go namedSize ty []
        SizeofExpr e                    -> sizeofExpr e
        UnaryExpr C.UopMinus e          -> rangeArith C.BopMinus (exactly 0) (go e)
        BinaryExpr a op b               -> rangeArith op (go a) (go b)
        _                               -> unknownRange

-- | Sizes of builtin types. Those that differ between platforms are ranges.
builtinSize :: Text -> Maybe Range
builtinSize = \case
    "float"  -> Just (exactly 4)
    "double" -> Just (exactly 8)
    name     -> itBytes <$> Map.lookup name intTypes

pointerSize :: Range
pointerSize = Range (Just 4) (Just 8)

-- | What a builtin type is aligned to in a struct: its size, but 8 byte
-- numbers are aligned to 4 on 32 bit x86.
builtinAlign :: Text -> Range
builtinAlign name = case builtinSize name of
    Just (Range (Just 8) (Just 8)) -> Range (Just 4) (Just 8)
    Just r                         -> r
    Nothing                        -> unknownRange

-- | The integer type a type is, through typedefs.
integerType :: Env -> CType -> Maybe IntType
integerType env ct =
    let t = resolveType env ct
    in if ctPointers t == 0 && null (ctDims t) then Map.lookup (ctName t) intTypes else Nothing

isIntegerType :: Env -> CType -> Bool
isIntegerType env = isJust . integerType env

-- | The type written in a declaration, without its dimensions.
typeOfDecl :: C.Node (Lexeme Text) -> CType
typeOfDecl (Fix node) = case node of
    TyStd (L _ _ n)         -> CType n 0 []
    TyUserDefined (L _ _ n) -> CType n 0 []
    TyStruct (L _ _ n)      -> CType n 0 []
    TyUnion (L _ _ n)       -> CType n 0 []
    TyFunc (L _ _ n)        -> CType n 0 []
    TyPointer t             -> let ct = typeOfDecl t in ct { ctPointers = ctPointers ct + 1 }
    TyConst t               -> typeOfDecl t
    TyNonnull t             -> typeOfDecl t
    TyNullable t            -> typeOfDecl t
    TyOwner t               -> typeOfDecl t
    TyBitwise t             -> typeOfDecl t
    TyForce t               -> typeOfDecl t
    _                       -> unknownType

-- | The type of a variable declaration, with its dimensions.
declType :: Env -> C.Node (Lexeme Text) -> Maybe (Text, CType)
declType env = declTypeWith env (const unknownRange)

-- | The type of a declaration whose dimensions may take the sizes of
-- expressions (@sizeof(buf)@).
declTypeWith :: Env -> (C.Node (Lexeme Text) -> Range) -> C.Node (Lexeme Text) -> Maybe (Text, CType)
declTypeWith env sizeofExpr (Fix node) = case node of
    VarDecl ty (L _ _ name) dims -> Just (name, (typeOfDecl ty) { ctDims = map (dimOf (envConstRangeWith env sizeofExpr)) dims })
    NonNullParam d               -> declTypeWith env sizeofExpr d
    NullableParam d              -> declTypeWith env sizeofExpr d
    _                            -> Nothing

-- | Bounds of a constant expression, from what every function can see.
envConstRange :: Env -> C.Node (Lexeme Text) -> Range
envConstRange env = envConstRangeWith env (const unknownRange)

envConstRangeWith :: Env -> (C.Node (Lexeme Text) -> Range) -> C.Node (Lexeme Text) -> Range
envConstRangeWith env = constRange (\n -> Map.findWithDefault unknownRange n (envConstants env)) (envNamedSize env)

-- | How many bytes a value of a type has: its elements' size times its
-- dimensions.
typeBytes :: Env -> CType -> Range
typeBytes env t =
    let t' = resolveType env t
        element = if ctPointers t' > 0 then pointerSize else envNamedSize env (ctName t')
    in foldl' (rangeArith C.BopMul) element (ctDims t')

envNamedSize :: Env -> Text -> Range
envNamedSize env n = fromMaybe (Map.findWithDefault unknownRange n (envTypeSizes env)) (builtinSize n)

typedefsOf :: Env -> C.Node (Lexeme Text) -> [(Text, CType)]
typedefsOf env (Fix node) = case node of
    Typedef (Fix (Struct (L _ _ s) _)) (L _ _ name) _ -> [(name, CType s 0 [])]
    Typedef (Fix (Union (L _ _ s) _)) (L _ _ name) _  -> [(name, CType s 0 [])]
    Typedef ty (L _ _ name) dims ->
        let ct = typeOfDecl ty
            dims' = map (dimOf (envConstRange env)) dims
        in [(name, ct { ctDims = dims' }) | ctName ct /= name || ctPointers ct > 0 || not (null dims')]
    FunctionDefn{} -> []
    _ -> concatMap (typedefsOf env) (toList node)

structsOf :: Env -> C.Node (Lexeme Text) -> [(Text, Map Text CType)]
structsOf env (Fix node) = case node of
    Struct (L _ _ name) members -> [(name, Map.fromList (concatMap member members))]
    Union (L _ _ name) members  -> [(name, Map.fromList (concatMap member members))]
    FunctionDefn{}              -> []
    _                           -> concatMap (structsOf env) (toList node)
  where
    member (Fix m) = case m of
        MemberDecl d _ -> maybe [] pure (declType env d)
        Commented _ d  -> member d
        _              -> concatMap member (toList m)

-- | The fields of each struct, in order, where its members are all fields
-- declared one by one.
fieldOrderOf :: C.Node (Lexeme Text) -> [(Text, [Text])]
fieldOrderOf (Fix node) = case node of
    Struct (L _ _ name) members -> [ (name, order) | Just order <- [concat <$> traverse member members] ]
    FunctionDefn{}              -> []
    _                           -> concatMap fieldOrderOf (toList node)
  where
    member (Fix m) = case m of
        MemberDecl (Fix (VarDecl _ (L _ _ f) _)) _ -> Just [f]
        Commented _ d                              -> member d
        _                                          -> Nothing

-- | The buffer fields of each struct that have a length field: one named
-- after it (@data@ and @data_length@), or one just called a length next to
-- it (@data@ and @length@). An array of things that aren't bytes has a count
-- named after it (@peers@ and @num_peers@ or @peers_count@). Either may also
-- have a capacity (@peers_capacity@).
pairsOf :: Env -> C.Node (Lexeme Text) -> [(Text, [FieldPair])]
pairsOf env (Fix node) = case node of
    Struct (L _ _ name) members -> [(name, pairs (concatMap member members))]
    FunctionDefn{}              -> []
    _                           -> concatMap (pairsOf env) (toList node)
  where
    member (Fix m) = case m of
        MemberDecl d _ -> maybe [] pure (declType env d)
        Commented _ d  -> member d
        _              -> concatMap member (toList m)
    pairs fields =
        [ pr
        | (i, (x, ty)) <- indexed
        , isBufferType env ty || isCountedType env ty
        , let named = [ n | (n, t) <- fields, isIntegerType env t
                          , isBufferType env ty && n `elem` map (x <>) ["_length", "_len", "_size"] || isCountedType env ty && isCountOf x n ]
              -- A bare length between 2 buffers is neither's.
              beside = [ n | isBufferType env ty, j <- [i - 1, i + 1], Just (n, t) <- [lookup j indexed]
                           , n `elem` ["length", "len", "size"], isIntegerType env t
                           , not (maybe False (isBufferType env . snd) (lookup (2 * j - i) indexed)) ]
              count = listToMaybe (named ++ beside)
        , pr <- case [ n | (n, t) <- fields, isIntegerType env t, n == x <> "_capacity" ] of
            capacity : _ -> [FieldPair x capacity count]
            []           -> maybe [] (\l -> [FieldPair x l Nothing]) count
        ]
      where
        indexed = zip [0 :: Int ..] fields

globalsOf :: Env -> C.Node (Lexeme Text) -> [(Text, CType)]
globalsOf env (Fix node) = case node of
    VarDeclStmt d _               -> maybe [] pure (declType env d)
    ConstDefn _ ty (L _ _ name) _ -> [(name, typeOfDecl ty)]
    FunctionDefn{}                -> []
    Struct{}                      -> []
    Union{}                       -> []
    _                             -> concatMap (globalsOf env) (toList node)

-- | Global variables that aren't const. Cimple calls every global with a
-- value a 'ConstDefn'.
mutableGlobalsOf :: C.Node (Lexeme Text) -> [Text]
mutableGlobalsOf (Fix node) = case node of
    ConstDefn _ ty (L _ _ name) _ | not (isConstType ty) -> [name]
    VarDeclStmt (Fix (VarDecl ty (L _ _ name) _)) _ | not (isConstType ty) -> [name]
    FunctionDefn{} -> []
    _ -> concatMap mutableGlobalsOf (toList node)

-- | Whether a declared type is const itself (not just what it points to).
isConstType :: C.Node (Lexeme Text) -> Bool
isConstType (Fix TyConst{}) = True
isConstType _               = False

-- | Signatures of prototypes (or definitions), and of function typedefs.
signaturesOf :: Env -> Bool -> C.Node (Lexeme Text) -> [(Text, Signature)]
signaturesOf env definitions (Fix node) = case node of
    FunctionDecl _ proto | not definitions -> signature proto
    FunctionDefn _ proto _ | definitions   -> signature proto
    TypedefFunction proto | not definitions -> signature proto
    FunctionDecl{} -> []
    FunctionDefn{} -> []
    TypedefFunction{} -> []
    _ -> concatMap (signaturesOf env definitions) (toList node)
  where
    signature proto = case unFix proto of
        FunctionPrototype ret (L _ _ name) params -> [(name, Signature (typeOfDecl ret) (paramsOf env params))]
        Commented _ p -> signature p
        _ -> []

paramsOf :: Env -> [C.Node (Lexeme Text)] -> [Maybe Param]
paramsOf env params =
    let named = [ x | p <- params, isDecl p, Just x <- [declType env p] ]
        lengths = map Just (drop 1 named) ++ [Nothing]
    in [ Just (Param ty ((i + 1 <$ lengthParam name ty next) <|> mostParam named name ty) (i + 1 <$ outLengthParam ty next))
       | (i, (name, ty), next) <- zip3 [0 ..] named lengths ]
       ++ [ Nothing | any isEllipsis params ]
  where
    unwrap (Fix (NonNullParam d))  = unwrap d
    unwrap (Fix (NullableParam d)) = unwrap d
    unwrap d                       = d
    isDecl p = case unFix (unwrap p) of
        VarDecl{} -> True
        _         -> False
    isEllipsis (Fix Ellipsis) = True
    isEllipsis _              = False
    -- A pointer named @*_ptr@ is to the one value a function gives back.
    -- An array of a fixed size has that many, whatever comes after it.
    lengthParam _ ty _ | Range (Just _) (Just _) : _ <- ctDims ty = Nothing
    lengthParam name ty next = case next of
        Just (n, nty)
            | isBufferType env ty && not ("_ptr" `T.isSuffixOf` name)
            , isIntegerType env nty && isLengthName n -> Just ()
            | isCountedType env ty, isIntegerType env nty, isCountOf name n -> Just ()
        _ -> Nothing
    -- A pointer to a buffer pointer, followed by a pointer to its length.
    outLengthParam ty next = case next of
        Just (n, nty)
            | ctPointers ty > 1 && null (ctDims ty) && isBufferType env (deref ty)
            , ctPointers nty > 0 && null (ctDims nty) && isIntegerType env (deref nty)
            , isLengthName (fromMaybe n (T.stripSuffix "_ptr" n)) -> Just ()
        _ -> Nothing
    deref t = t { ctPointers = ctPointers t - 1 }
    isLengthName n = n `elem` ["length", "len", "size"] || any (`T.isSuffixOf` n) ["_length", "_len", "_size"]
    -- The most an array may hold: @max_x@ or @max_num_x@, wherever it is.
    mostParam named name ty
        | Range (Just _) (Just _) : _ <- ctDims ty = Nothing
        | isCountedType env ty = listToMaybe
            [ j | (j, (n, nty)) <- zip [0 ..] named, n `elem` ["max_" <> name, "max_num_" <> name], isIntegerType env nty ]
        | otherwise = Nothing

-- | An array of something that isn't counted in bytes (not @void@), so a
-- count of it is of its elements.
isCountedType :: Env -> CType -> Bool
isCountedType env ty = case ctDims ty of
    _ : _ -> True
    []    -> ctPointers ty > 0 && resolveType env ty { ctPointers = ctPointers ty - 1 } /= CType "void" 0 []

-- | Whether a name is that of a count of an array: @num_x@ or @x_count@.
isCountOf :: Text -> Text -> Bool
isCountOf x n = n == "num_" <> x || n == x <> "_count"

-- | A buffer of integers (bytes, chars, numbers): a pointer to an object
-- followed by a size is something else.
isBufferType :: Env -> CType -> Bool
isBufferType env ty = case ctDims ty of
    _ : ds -> isIntegerType env ty { ctDims = ds }
    []     -> ctPointers ty > 0 && (isIntegerType env pointee || pointee == CType "void" 0 [])
  where
    pointee = resolveType env ty { ctPointers = ctPointers ty - 1 }

-- | Whether a type is counted in bytes: @void@ and the 1 byte integers.
isByteType :: Env -> CType -> Bool
isByteType env t =
    let t' = resolveType env t
    in ctPointers t' == 0 && null (ctDims t') && (ctName t' == "void" || maybe False ((== exactly 1) . itBytes) (integerType env t'))

-- | The libc functions on buffers: each buffer has the bytes the length
-- after them says.
builtinFunctions :: Map Text Signature
builtinFunctions = Map.fromList
    [ ("memcpy", Signature voidPtr [buffer 2, buffer 2, size])
    , ("memmove", Signature voidPtr [buffer 2, buffer 2, size])
    , ("memcmp", Signature (CType "int" 0 []) [buffer 2, buffer 2, size])
    , ("memset", Signature voidPtr [buffer 2, Just (Param (CType "int" 0 []) Nothing Nothing), size])
    , ("malloc", Signature voidPtr [size])
    , ("calloc", Signature voidPtr [size, size])
    , ("realloc", Signature voidPtr [Just (Param voidPtr Nothing Nothing), size])
    ]
  where
    voidPtr = CType "void" 1 []
    buffer len = Just (Param voidPtr (Just len) Nothing)
    size = Just (Param (CType "size_t" 0 []) Nothing Nothing)

-- | The C library's allocators, and which arguments give the size of what
-- they return.
builtinAllocSizes :: Map Text [Int]
builtinAllocSizes = Map.fromList [("malloc", [1]), ("calloc", [1, 2]), ("realloc", [2])]

-- | Follows typedefs to what they stand for.
resolveType :: Env -> CType -> CType
resolveType env = go (10 :: Int)
  where
    go 0 t = t
    go n t = case Map.lookup (ctName t) (envTypedefs env) of
        Just u | ctName u /= ctName t || not (null (ctDims u)) ->
            go (n - 1) u { ctPointers = ctPointers u + ctPointers t, ctDims = ctDims t ++ ctDims u }
        _ -> t

isPointerType :: CType -> Bool
isPointerType t = ctPointers t > 0 || not (null (ctDims t))

-- | The type of an expression, given the types of the variables it can
-- see.
typeOfExpr :: Env -> Map Text CType -> C.Node (Lexeme Text) -> Maybe CType
typeOfExpr env types = fmap (resolveType env) . go
  where
    go (Fix node) = case node of
        VarExpr (L _ _ v) -> Map.lookup v types
        ParenExpr e -> go e
        CastExpr ty _ -> Just (typeOfDecl ty)
        PointerAccess e (L _ _ f) -> go e >>= field f . deref . resolveType env
        MemberAccess e (L _ _ f) -> go e >>= field f . resolveType env
        ArrayAccess e _ -> index . resolveType env <$> go e
        UnaryExpr C.UopDeref e -> deref . resolveType env <$> go e
        UnaryExpr C.UopAddress e -> (\t -> t { ctPointers = ctPointers t + 1 }) <$> go e
        FunctionCall (Fix (VarExpr (L _ _ f))) _ -> sigReturn <$> Map.lookup f (envFunctions env)
        -- The distance between 2 pointers is a number.
        BinaryExpr a C.BopMinus b
            | Just t <- go a, isPointerType t, Just u <- go b, isPointerType u -> Just (CType "ptrdiff_t" 0 [])
        BinaryExpr a op b | op `elem` [C.BopPlus, C.BopMinus] ->
            case (go a, go b) of
                (Just t, _) | isPointerType t -> Just t
                (_, Just t) | isPointerType t -> Just t
                (t, _)                        -> t
        TernaryExpr _ a b -> go a <|> go b
        LiteralExpr C.String _ -> Just (CType "char" 1 [])
        _ -> Nothing
    field f t = Map.lookup (ctName t) (envStructs env) >>= Map.lookup f
    deref t = case ctDims t of
        (_:ds) -> t { ctDims = ds }
        []     -> t { ctPointers = max 0 (ctPointers t - 1) }
    index = deref

-- | A function's local variables. An array's size may be that of variables
-- declared before it (@uint8_t packet[1 + sizeof(plain)]@).
localsOf :: Env -> Map Text CType -> C.Node (Lexeme Text) -> [(Text, CType)]
localsOf env outer body = reverse (foldl' add [] (subnodes body))
  where
    -- An array declared without a size has as many elements as it's given.
    given = Map.fromList
        [ (name, length es)
        | Fix (VarDeclStmt (Fix (VarDecl _ (L _ _ name) (Fix (DeclSpecArray _ Nothing) : _))) (Just (Fix (InitialiserList es)))) <- subnodes body
        ]
    add acc n@(Fix node) = case node of
        VarDecl{} | Just (name, t) <- declTypeWith env (sizeofIn acc) n ->
            let t' = case (Map.lookup name given, ctDims t) of
                    (Just k, _ : ds) -> t { ctDims = exactly (fromIntegral k) : ds }
                    _                -> t
            in (name, t') : acc
        VLA ty (L _ _ name) _ -> (name, (typeOfDecl ty) { ctDims = [unknownRange] }) : acc
        _ -> acc
    sizeofIn acc (Fix e) = case e of
        ParenExpr x -> sizeofIn acc x
        VarExpr (L _ _ v) | Just t <- lookup v acc <|> Map.lookup v outer -> typeBytes env t
        _ -> unknownRange

-- | A node and every node in it.
subnodes :: C.Node (Lexeme Text) -> [C.Node (Lexeme Text)]
subnodes n = go n []
  where
    go x rest = x : foldr go rest (unFix x)

isNullptr :: C.Node (Lexeme Text) -> Bool
isNullptr (Fix node) = case node of
    LiteralExpr C.ConstId (L _ _ "nullptr") -> True
    ParenExpr e                             -> isNullptr e
    _                                       -> False
