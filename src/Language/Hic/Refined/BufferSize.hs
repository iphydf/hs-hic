{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}

-- | Buffer sizes, followed through each function: an argument for an array
-- parameter with a size (@x[_Nonnull SIZE]@) must have at least that many
-- elements.
--
-- A pointer's size comes from what it was made from: an array, an array
-- parameter, a pointer parameter followed by its length, a field that is an
-- array, or what a function returns. Pointer arithmetic takes from it, and
-- guards on lengths (@if (length < 33) return -1;@) tell how much there is.
--
-- Fields are followed like variables. A buffer field with a length field
-- (@data@ and @data_length@) has as many elements as the length says
-- wherever it's read, which is checked wherever something else can see
-- them: at calls given what they're in, and where the function returns.
module Language.Hic.Refined.BufferSize
    ( checkBufferSizes
    , Sizes
    , sizeSummaries
    , analyseBufferSizes
    , sizeErrors
    , leastBefore
    , Known (..)
    ) where

import           Control.Applicative                      ((<|>))
import           Control.Monad                            (guard)
import           Control.Monad.Identity                   (Identity (..))
import           Data.Fix                                 (Fix (..), foldFix,
                                                           unFix)
import           Data.Foldable                            (toList)
import           Data.Function                            ((&))
import qualified Data.Graph                               as Graph
import           Data.List                                (isPrefixOf, nub)
import           Data.Map.Strict                          (Map)
import qualified Data.Map.Strict                          as Map
import           Data.Maybe                               (catMaybes, fromMaybe,
                                                           isJust, isNothing,
                                                           listToMaybe,
                                                           mapMaybe)
import qualified Data.Set                                 as Set
import           Data.Text                                (Text)
import qualified Data.Text                                as T
import           Language.Cimple                          (Lexeme (..),
                                                           NodeF (..))
import qualified Language.Cimple                          as C
import           Language.Cimple.Pretty                   (showNodePlain)
import           Language.Hic.Core.AstUtils               (getAlexPosn,
                                                           getLexeme)
import           Language.Hic.Core.DataFlow               (CFG, CFGNode (..),
                                                           DataFlow (..),
                                                           buildCFG, fixpoint)
import           Language.Hic.Core.Errors                 (Context (..),
                                                           ErrorInfo (..),
                                                           TypeError (..))
import           Language.Hic.Refined.BufferSize.Env
import           Language.Hic.Refined.BufferSize.Escape
import           Language.Hic.Refined.BufferSize.Facts
import           Language.Hic.Refined.BufferSize.Integers
import           Language.Hic.Refined.BufferSize.Paths
import           Language.Hic.Refined.Effects             (Effects (..), Loc,
                                                           Summaries,
                                                           callEffects,
                                                           footprint, mayChange,
                                                           ownArrayIn,
                                                           rawStructs,
                                                           scopeMacros,
                                                           summarise, targetsOf)
import qualified Language.Hic.Refined.Inference.Platform  as Platform
import           Text.Read                                (readMaybe)

------------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------------

-- | What one function's analysis needs.
data FunctionCtx l = FunctionCtx
    { fcEnv       :: Env
    , fcTypes     :: Map Text CType
      -- ^ Parameters, locals and globals.
    , fcParams    :: Set.Set Text
      -- ^ Its parameters: one that's an array points to at least so many.
    , fcArgs      :: [Text]
      -- ^ The same, in order.
    , fcEscaped   :: Set.Set Text
      -- ^ Variables that a call or a store through a pointer may change:
      -- those whose address is taken, local arrays named where their
      -- elements may be kept, and globals.
    , fcPaths     :: Map Text PathInfo
      -- ^ The places in memory the function names, followed like variables.
    , fcPairs     :: [Pair]
    , fcLoc       :: Maybe (Lexeme Text)
      -- ^ The function's name, for what's checked where it ends.
    , fcIndex     :: PathIndex
    , fcSummaries :: Summaries
      -- ^ Where each function may store.
    , fcAliases   :: Map Text Path
      -- ^ Pointer variables that only ever point to one place, given by a
      -- call ('envReturnsPlace'): the place.
    , fcCompared  :: Set.Set Text
      -- ^ Variables compared with a constant by @==@ or @!=@: those that
      -- may be told apart from a number for none ('givenNone').
    }

-- | The paths and pairs of a function, looked up in the ways the analysis
-- needs.
data PathIndex = PathIndex
    { ixWith    :: Map Text [Text]
      -- ^ By the variables their place depends on.
    , ixByRoot  :: Map Text [(Text, Path)]
    , ixPairsOf :: Map Text [Pair]
      -- ^ By either of their members.
    , ixEscaped :: [Text]
      -- ^ Those from variables any code may have the address of.
    }

pathIndex :: Set.Set Text -> Map Text PathInfo -> [Pair] -> PathIndex
pathIndex escaped paths pairs = PathIndex
    { ixWith = Map.fromListWith (++) [ (v, [n]) | (n, info) <- named, v <- nub (pathVars (piPath info)) ]
    , ixByRoot = Map.fromListWith (++) [ (pathRoot (piPath info), [(n, piPath info)]) | (n, info) <- named ]
    , ixPairsOf = Map.fromListWith (++) [ (n, [pr]) | pr <- pairs, n <- prBuffer pr : prLength pr : toList (prCount pr) ]
    , ixEscaped = [ n | (n, info) <- named, pathRoot (piPath info) `Set.member` escaped ]
    }
  where
    named = Map.toList paths

data PathInfo = PathInfo
    { piPath     :: Path
    , piFoot     :: [Loc]
      -- ^ What a store may change it through ('footprint').
    , piType     :: Maybe CType
    , piOutlives :: Bool
      -- ^ Whether it's in memory that outlives the function: a global, or
      -- through a pointer.
    }

-- | A buffer kept with its length: a field and its length field, or what
-- out-parameters for both point to.
data Pair = Pair
    { prBuffer     :: Text
    , prLength     :: Text
    , prElements   :: Maybe Integer
      -- ^ An array's, which has them whatever the length says.
    , prLengthType :: Maybe IntType
    , prOutlives   :: Bool
    , prCount      :: Maybe Text
      -- ^ How many of the elements are used, if the length is a capacity.
    , prCountType  :: Maybe IntType
    }
    deriving (Eq)

instance DataFlow Identity FunctionCtx Text Facts () where
    emptyFacts _ = return Unreached
    join ctx a b = return (joinFacts (sizeHints ctx) a b)
    joinLoop ctx a b = return (joinLoopFacts (sizeHints ctx) [] a b)
    joinLoopHead ctx stmts before round' = return (keepingEntry (unchangedIn ctx stmts) before (joinLoopFacts (sizeHints ctx) (stepGuesses ctx before stmts) before round'))
    widen ctx old new = return (withinTypes ctx (widenFacts old new))
    widenLoop ctx stmts old new = return (withinTypes ctx (widenFactsKeeping (unchangedIn ctx stmts) old new))
    transfer ctx _ _ facts stmt = return (transferStmt ctx facts stmt, Set.empty)

-- | What a loop's steps say may stay so far apart, to be checked where it
-- starts and each time round ('joinLoopFacts'): something it only adds to,
-- at least k each time if each step it takes is, against a counter it only
-- adds 1 to. A pointer moved is its offset ('offsetVar').
stepGuesses :: FunctionCtx Text -> Facts -> [C.Node (Lexeme Text)] -> [(Text, Text, Integer)]
stepGuesses _ Unreached _ = []
stepGuesses ctx facts stmts =
    [ (named w, named u, k)
    | (u, Just 1) <- Map.toList totals
    , (w, Just k) <- Map.toList totals
    , k > 1
    ]
  where
    nodes = concatMap subnodes stmts
    steps = Map.fromListWith (++) [ (v, [d]) | Fix n <- nodes, Just (v, d) <- [stepOf n] ]
    others = Set.fromList [ v | Fix n <- nodes, Nothing <- [stepOf n], v <- storedBy n ]
    totals = Map.map (fmap sum . sequence) (Map.withoutKeys steps others)
    named v = case Map.lookup v (fcTypes ctx) of
        Just t | isPointerType (resolveType (fcEnv ctx) t) -> offsetVar v
        _                                                  -> v
    -- How much a step adds at least, if it never takes away.
    stepOf = \case
        UnaryExpr C.UopIncr (Fix (VarExpr (L _ _ v))) -> Just (v, Just 1)
        UnaryExpr C.UopDecr (Fix (VarExpr (L _ _ v))) -> Just (v, Nothing)
        AssignExpr (Fix (VarExpr (L _ _ v))) C.AopPlus e -> Just (v, rLow (rangeOf ctx facts e) >>= \d -> if d >= 0 then Just d else Nothing)
        AssignExpr (Fix (VarExpr (L _ _ v))) C.AopMinus _ -> Just (v, Nothing)
        _ -> Nothing
    storedBy = \case
        AssignExpr (Fix (VarExpr (L _ _ v))) _ _         -> [v]
        UnaryExpr C.UopAddress (Fix (VarExpr (L _ _ v))) -> [v]
        VarDeclStmt (Fix (VarDecl _ (L _ _ v) _)) _      -> [v]
        _                                                -> []

-- | Facts whose integers are no wider than their types hold: a bound given
-- up by widening is the type's.
withinTypes :: FunctionCtx Text -> Facts -> Facts
withinTypes _ Unreached = Unreached
withinTypes ctx facts = facts { fInts = Map.mapWithKey clamp (fInts facts) }
  where
    clamp v r = maybe r (intersectRange r . itCanHold) (typeOfPlace ctx v >>= integerType (fcEnv ctx))

-- | The function's own variables a loop doesn't change: nothing else can
-- reach them, and in the loop they're not given anything, moved, pointed
-- to or declared.
unchangedIn :: FunctionCtx Text -> [C.Node (Lexeme Text)] -> Set.Set Text
unchangedIn ctx stmts = Set.fromList
    [ v
    | v <- Map.keys (fcTypes ctx)
    , Set.notMember v changed
    , Set.notMember v (fcEscaped ctx)
    , not (Map.member v (envGlobals (fcEnv ctx)))
    ]
  where
    changed = Set.fromList (concatMap changes (concatMap subnodes stmts))
    changes (Fix node) = case node of
        AssignExpr x _ _                                              -> named x
        UnaryExpr o x | o `elem` [C.UopIncr, C.UopDecr, C.UopAddress] -> named x
        VarDeclStmt (Fix (VarDecl _ (L _ _ v) _)) _                   -> [v]
        VLA _ (L _ _ v) _                                             -> [v]
        _                                                             -> []
    named (Fix node) = case node of
        VarExpr (L _ _ v) -> [v]
        ParenExpr x       -> named x
        _                 -> []

-- | Whether a path is in its variable's own memory: fields of structs and
-- elements of arrays it holds, never through a pointer.
inOwnMemory :: FunctionCtx Text -> Path -> Bool
inOwnMemory ctx (Path root steps) = maybe False (go steps . resolveType env) (Map.lookup root (fcTypes ctx))
  where
    env = fcEnv ctx
    go [] _ = True
    go (step : rest) t = case step of
        Field f | ctPointers t == 0, null (ctDims t) ->
            maybe False (go rest . resolveType env) (Map.lookup (ctName t) (envStructs env) >>= Map.lookup f)
        Index{} | _ : dims <- ctDims t -> go rest t { ctDims = dims }
        _ -> False

exprType :: FunctionCtx Text -> C.Node (Lexeme Text) -> Maybe CType
exprType ctx = typeOfExpr (fcEnv ctx) (fcTypes ctx)

-- | How many elements an array type has.
arrayElements :: CType -> Maybe Size
arrayElements t = case ctDims t of
    (Range (Just n) _ : _) -> Just (elements n)
    _                      -> Nothing

-- | Where a pointer expression points: the origin of its buffer, how far it
-- is from there, and how many elements the buffer has from the origin.
cursorOf :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Maybe (Text, Lin, Size)
cursorOf _ Unreached _ = Nothing
cursorOf ctx facts e@(Fix node) = case node of
    ParenExpr x -> cursorOf ctx facts x
    CastExpr ty x | sameElements ctx (typeOfDecl ty) (exprType ctx x) -> cursorOf ctx facts x
    _ | Just v <- placeOf ctx e, Just (Pointer o base) <- Map.lookup v (fPointers facts) ->
        Just (o, linVar (offsetVar v), base)
    VarExpr (L _ _ v) | Just size <- exprType ctx e >>= arrayElements -> Just (arrayOrigin v, linConstant 0, size)
    BinaryExpr a C.BopPlus b
        | pointerSide ctx facts a, Just k <- formOf ctx facts b -> moved k <$> cursorOf ctx facts a
        | pointerSide ctx facts b, Just k <- formOf ctx facts a -> moved k <$> cursorOf ctx facts b
    UnaryExpr C.UopAddress (Fix (ArrayAccess a i)) | Just k <- formOf ctx facts i ->
        moved k <$> cursorOf ctx facts a
    _ -> Nothing
  where
    moved k (o, off, base) = (o, off `linPlus` k, base)

pointerSide :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Bool
pointerSide ctx facts x = maybe (isJust (sizeOf ctx facts x)) isPointerType (exprType ctx x)

sameElements :: FunctionCtx Text -> CType -> Maybe CType -> Bool
sameElements ctx t (Just u) =
    let t' = elementOf (resolveType env t)
        u' = elementOf (resolveType env u)
    in t' == u' || (isByteType env t' && isByteType env u')
  where
    env = fcEnv ctx
sameElements _ _ Nothing = False

-- | What a pointer or array type's elements are.
elementOf :: CType -> CType
elementOf ty = case ctDims ty of
    _ : ds -> ty { ctDims = ds }
    []     -> ty { ctPointers = max 0 (ctPointers ty - 1) }

-- | How many bytes a value of a type has, as a sum: a number, or a symbol
-- for the size of a type that differs between platforms or with padding,
-- times the dimensions.
bytesLin :: Env -> CType -> Maybe Lin
bytesLin env t0 = do
    let t = resolveType env t0
        element = t { ctDims = [] }
    counts <- traverse exact (ctDims t)
    base <- case exact (typeBytes env element) of
        Just n  -> Just (linConstant n)
        Nothing -> linVar (sizeofName element) <$ rLow (typeBytes env element)
    return (linScale (product counts) base)
  where
    exact (Range (Just lo) (Just hi)) | lo == hi = Just lo
    exact _                                      = Nothing

-- | The symbol for the size of a type.
sizeofName :: CType -> Text
sizeofName t = "sizeof(" <> ctName t <> T.replicate (ctPointers t) "*" <> ")"

-- | A pointer expression's size in bytes. A pointer to something of which
-- only the type is known points to at least one.
bytesOf :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Maybe Size
bytesOf ctx facts e = case sizeOf ctx facts e of
    Just NullPointer -> Just NullPointer
    size -> case resolveType env <$> exprType ctx e of
        Just t | isPointerType t, not (isByteType env (elementOf t)) -> do
            each <- bytesLin env (elementOf t)
            case fromMaybe (elements 1) size of
                NullPointer -> Just NullPointer
                Size l
                    | Map.null (linVars l) -> Just (Size (linScale (linConst l) each))
                    | Map.null (linVars each) -> Just (Size (linScale (linConst each) l))
                    | otherwise -> (\n -> Size (linScale n each)) <$> lowerLin facts l
        _ -> size
  where
    env = fcEnv ctx

-- | An argument's size in what the parameter counts: bytes for a buffer of
-- bytes, else its own elements.
argumentSize :: FunctionCtx Text -> Facts -> Param -> C.Node (Lexeme Text) -> Maybe Size
argumentSize ctx facts param arg
    | isByteType (fcEnv ctx) (elementOf (resolveType (fcEnv ctx) (paramType param))) = bytesOf ctx facts arg
    | otherwise = sizeOf ctx facts arg

sizeOf :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Maybe Size
sizeOf _ Unreached _ = Nothing
sizeOf ctx facts e@(Fix node) = case cursorOf ctx facts e of
    Just (_, off, Size base) -> Just (Size (base `linMinus` off))
    Just (_, _, NullPointer) -> Just NullPointer
    Nothing -> case node of
        ParenExpr x -> sizeOf ctx facts x
        CastExpr ty x
            | Just sz <- allocated ctx facts (typeOfDecl ty) x -> Just sz
            | sameElements ctx (typeOfDecl ty) (exprType ctx x) -> sizeOf ctx facts x
            -- Something seen as bytes has as many as its size.
            | isByteType (fcEnv ctx) (elementOf (resolveType (fcEnv ctx) (typeOfDecl ty))) -> bytesOf ctx facts x
            | otherwise -> Nothing
        BinaryExpr a C.BopPlus b
            | pointerSide ctx facts a -> sizeOf ctx facts a >>= advance (rangeOf ctx facts b)
            | pointerSide ctx facts b -> sizeOf ctx facts b >>= advance (rangeOf ctx facts a)
        UnaryExpr C.UopAddress (Fix (ArrayAccess a i)) ->
            sizeOf ctx facts a >>= advance (rangeOf ctx facts i)
        UnaryExpr C.UopAddress _ -> Just (elements 1)
        FunctionCall f _
            | Just (_, sig) <- signatureOf ctx f, Just sz <- allocated ctx facts (sigReturn sig) e -> Just sz
        FunctionCall (Fix (VarExpr (L _ _ f))) _ | Map.notMember f (fcTypes ctx) -> elements <$> Map.lookup f (envReturns (fcEnv ctx))
        -- Through a pointer: the least any function given as its type gives.
        FunctionCall f _ -> elements <$> returnedThrough ctx f
        PointerAccess{} | Just n <- fieldKey ctx e >>= (`Map.lookup` envFields (fcEnv ctx)) -> Just (elements n)
        MemberAccess{} | Just n <- fieldKey ctx e >>= (`Map.lookup` envFields (fcEnv ctx)) -> Just (elements n)
        _ | isNullptr e -> Just NullPointer
        TernaryExpr _ a b -> case (sizeOf ctx facts a, sizeOf ctx facts b) of
            (Just NullPointer, y) -> y
            (x, Just NullPointer) -> x
            (x, y)                -> do
                x' <- x >>= lowerBound facts
                y' <- y >>= lowerBound facts
                return (elements (min x' y'))
        _ -> exprType ctx e >>= arrayElements

-- | The size of allocated memory, as the type it's cast to or returned as:
-- in elements of that type. An allocation of n times @sizeof(T)@ cast to
-- @T *@ has n.
allocated :: FunctionCtx Text -> Facts -> CType -> C.Node (Lexeme Text) -> Maybe Size
allocated ctx facts ty (Fix node) = case node of
    ParenExpr x -> allocated ctx facts ty x
    FunctionCall f args -> do
        (name, _) <- signatureOf ctx f
        positions <- Map.lookup name (envAllocSizes env)
        sizeArgs <- traverse (\i -> lookup i (zip [1 ..] args)) positions
        let target = resolveType env ty
        guard (ctPointers target > 0)
        let element = target { ctPointers = ctPointers target - 1 }
            elementSize = if ctPointers element > 0 then pointerSize else envNamedSize env (ctName element)
            ofElements arg = case unFix arg of
                SizeofType t -> resolveType env (typeOfDecl t) == element
                _            -> False
        case sizeArgs of
            [count, each] | ofElements each -> Size <$> formOf ctx facts count
            _ | elementSize == exactly 1, [bytes] <- sizeArgs -> Size <$> formOf ctx facts bytes
            _ -> do
                bytes <- product <$> traverse (rLow . rangeOf ctx facts) sizeArgs
                most <- rHigh elementSize
                guard (most > 0)
                return (elements (bytes `div` most))
    _ -> Nothing
  where
    env = fcEnv ctx

-- | The struct and field an access is of.
fieldKey :: FunctionCtx Text -> C.Node (Lexeme Text) -> Maybe (Text, Text)
fieldKey ctx (Fix node) = case node of
    PointerAccess b (L _ _ f) -> (\t -> (ctName t, f)) . resolveType (fcEnv ctx) <$> exprType ctx b
    MemberAccess b (L _ _ f)  -> (\t -> (ctName t, f)) . resolveType (fcEnv ctx) <$> exprType ctx b
    _                         -> Nothing

-- | What's known of an integer expression: its type, its bounds, the sum
-- of variables it is with the fewest bits that sum is right modulo
-- ('Nothing' if it's right), and other sums it's at most. A sum or
-- difference that wraps is still right modulo 2 to the power of the bits of
-- the type it's done in.
data IntValue = IntValue
    { ivType    :: Maybe IntType
    , ivRange   :: ~Range
    , ivForm    :: ~(Maybe (Lin, Maybe Integer))
    , ivAtMost  :: ~[Lin]
    , ivAtLeast :: ~[Lin]
      -- ^ Sums of variables the value is at least.
    }

-- | A value of which only the bounds are known; one value is a constant.
bounded :: Maybe IntType -> Range -> IntValue
bounded t r = IntValue t r form [] []
  where
    form = case r of
        Range (Just lo) (Just hi) | lo == hi -> Just (linConstant lo, Nothing)
        _                                    -> Nothing

exactForm :: IntValue -> Maybe Lin
exactForm iv = case ivForm iv of
    Just (l, Nothing) -> Just l
    _                 -> Nothing

-- | Sums of variables the value is at most: the one it is, or one it's
-- right modulo 2 to the power of n of, if that sum is at least 0 and the
-- value is from 0 to below 2 to the n (a value that has lost bits that way
-- is smaller), and the others known.
upperForms :: Facts -> IntValue -> [Lin]
upperForms facts iv = own ++ ivAtMost iv
  where
    own = case ivForm iv of
        Just (l, Nothing) -> [l]
        Just (l, Just bits)
            | maybe False (>= 0) (lowerLin facts l)
            , ivRange iv `within` Range (Just 0) (Just (2 ^ bits - 1)) -> [l]
        _ -> []

-- | Sums of variables the value is at least: the one it is, and the others
-- known.
lowerForms :: IntValue -> [Lin]
lowerForms iv = maybe id (:) (exactForm iv) (ivAtLeast iv)

intValue :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> IntValue
intValue _ Unreached _ = IntValue Nothing unknownRange Nothing [] []
intValue ctx facts e@(Fix node) = case node of
    VarExpr (L _ _ v)
        | Just ty <- Map.lookup v (fcTypes ctx) ->
            let t = integerType env ty
            in IntValue t (maybe id (intersectRange . itCanHold) t (Map.findWithDefault unknownRange v (fInts facts))) ((linVar v, Nothing) <$ t) [] []
        | otherwise -> constant v
    _ | Just (n, info) <- trackedPath ctx e, Just t <- piType info >>= integerType env ->
        IntValue (Just t) (intersectRange given (pathRange t n facts)) (Just (linVar n, Nothing)) [] []
    LiteralExpr C.Bool (L _ _ "true") -> bounded (Map.lookup "bool" intTypes) (exactly 1)
    LiteralExpr C.Bool (L _ _ "false") -> bounded (Map.lookup "bool" intTypes) (exactly 0)
    LiteralExpr C.ConstId (L _ _ v) -> constant v
    LiteralExpr C.Int (L _ _ t) -> bounded (literalType t) (maybe unknownRange exactly (parseIntLiteral t))
    ParenExpr x -> value x
    CastExpr ty x -> convertValue ctx facts (integerType env (typeOfDecl ty)) (value x)
    SizeofType t -> sizeofValue (typeOfDecl t) (envConstRange env e)
    -- An array as long as a sum is that many times its element's size.
    SizeofExpr x
        | Just v <- placeOf ctx x
        , Just (Pointer o (Size l)) <- Map.lookup v (fPointers facts)
        , o == arrayOrigin v
        , Just t <- resolveType env <$> exprType ctx x
        , not (null (ctDims t))
        , Range (Just k) (Just k') <- typeBytes env t { ctDims = drop 1 (ctDims t) }
        , k == k'
        , let bytes = linScale k l
        -> IntValue (Just sizeType) (rangeOfLin facts bytes) (Just (bytes, Nothing)) [] []
    SizeofExpr x -> maybe (bounded (Just sizeType) unknownRange) (\t -> sizeofValue t (typeBytes env t)) (exprType ctx x)
    UnaryExpr C.UopMinus x ->
        let ix = value x
            t = promote <$> ivType ix
        in arithmetic t C.BopMinus (bounded t (exactly 0)) (convertValue ctx facts t ix)
    -- How many elements an array has: its size over its first element's.
    BinaryExpr (Fix (SizeofExpr a)) C.BopDiv (Fix (SizeofExpr el))
        | Just k <- elementsOf a el -> bounded (Just sizeType) (exactly k)
    BinaryExpr a C.BopMinus b
        | pointerSide ctx facts a && pointerSide ctx facts b ->
            case (cursorOf ctx facts a, cursorOf ctx facts b) of
                (Just (oa, offA, _), Just (ob, offB, _)) | oa == ob && comparableOrigin oa ->
                    let l = offA `linMinus` offB
                    in IntValue (Just ptrdiffType) (rangeOfLin facts l `intersectRange` itCanHold ptrdiffType) (Just (l, Nothing)) [] []
                _ -> bounded (Just ptrdiffType) (itCanHold ptrdiffType)
    BinaryExpr a op b
        | pointerSide ctx facts a || pointerSide ctx facts b -> IntValue Nothing unknownRange Nothing [] []
        | otherwise ->
            let ia = value a
                ib = value b
                t = binaryType op (ivType ia) (ivType ib)
            in if isJust (comparison op) || op `elem` [C.BopAnd, C.BopOr]
               then bounded t (Range (Just 0) (Just 1))
               else arithmetic t op (convertValue ctx facts t ia) (convertValue ctx facts t ib)
    -- A string is shorter than the array it's in, which holds its
    -- terminator too.
    FunctionCall (Fix (VarExpr (L _ _ "strlen"))) [s]
        | Just n <- wholeArray s ->
            (bounded (Just sizeType) (Range (Just 0) (Just (n - 1)))) { ivAtMost = [linConstant (n - 1)] }
    -- Less than an argument of at least 1, else 0.
    FunctionCall f args
        | Just k <- callBelow ctx f
        , arg : _ <- drop k args
        , let t = exprType ctx e >>= integerType env
        , let ia = value arg ->
            let hi = maybe (rHigh (maybe unknownRange itCanHold t)) (Just . max 0 . subtract 1) (rHigh (ivRange ia))
                positive = maybe False (>= 1) (rLow (ivRange ia)) || maybe False (>= 1) (exactForm ia >>= lowerLin facts)
            in (bounded t (Range (Just 0) hi)) { ivAtMost = [ l `linMinus` linConstant 1 | positive, Just l <- [exactForm ia] ] }
    FunctionCall fe@(Fix (VarExpr (L _ _ f))) args ->
        let sig = Map.lookup f (envFunctions env)
            -- The operating system's functions in 'Platform.returnsAtMost' return an int.
            t = (sig >>= integerType env . sigReturn) <|> (intType <$ guard (isNothing sig && not (Map.null (Platform.returnsAtMost f))))
            atMost = maybe (systemAtMost f args) (returnedAtMost f args) sig ++ placedAtMost fe f args
            returned = Map.findWithDefault (maybe unknownRange itCanHold t) f (envIntReturns env)
            -- A number of at least 0 at most what the type holds here is
            -- returned as it is: it's that or a failure.
            range = case (Map.lookup f (envFailures env), mapMaybe (upperLin facts) atMost, t) of
                (Just fails, most@(_ : _), Just it)
                    | Just top <- rHigh (itHolds it), minimum most <= top ->
                        intersectRange returned (foldl' hull (Range (Just 0) (Just (minimum most))) fails)
                _ -> returned
        in (bounded t range) { ivAtMost = atMost }
    -- At most a sum each side is at most, and at least one each side is at
    -- least, under its condition.
    TernaryExpr c a b ->
        let ia = value a
            ib = value b
            t = commonType <$> ivType ia <*> ivType ib
            sides = [ (fs, convertValue ctx fs t (intValue ctx fs x))
                    | (truth, x) <- [(True, a), (False, b)], let fs = narrow ctx truth c facts ]
            uppers = [ (fs, upperForms fs iv) | (fs, iv) <- sides ]
            lowers = [ (fs, lowerForms iv) | (fs, iv) <- sides ]
            atMost u (fs, ls) = fs == Unreached || any (\l -> maybe False (>= 0) (lowerLin fs (u `linMinus` l))) ls
            atLeast u (fs, ls) = fs == Unreached || any (\l -> maybe False (>= 0) (lowerLin fs (l `linMinus` u))) ls
        in (bounded t (hull (ivRange (convertValue ctx facts t ia)) (ivRange (convertValue ctx facts t ib))))
            { ivAtMost = [ u | u <- nub (concatMap snd uppers), all (atMost u) uppers ]
            , ivAtLeast = [ u | u <- nub (concatMap snd lowers), all (atLeast u) lowers ]
            }
    _ -> let t = exprType ctx e >>= integerType env in bounded t (intersectRange given (maybe unknownRange itCanHold t))
  where
    -- The array an expression names, and its element (@a[0]@ or @*a@) by
    -- the other: the array's first dimension if it's one number.
    elementsOf a el = do
        t <- resolveType env <$> exprType ctx (unParen a)
        Range (Just k) (Just k') : _ <- Just (ctDims t)
        guard (k == k' && elementOf' (unParen el) (unParen a))
        return k
    elementOf' (Fix el) arr = case el of
        ArrayAccess b _        -> sameExpr b arr
        UnaryExpr C.UopDeref b -> sameExpr b arr
        _                      -> False
    sameExpr x y = showNodePlain (unParen x) == showNodePlain (unParen y)
    unParen (Fix (ParenExpr x)) = unParen x
    unParen x                   = x
    env = fcEnv ctx
    -- What a field is ever given.
    given = fromMaybe unknownRange (fieldKey ctx e >>= (`Map.lookup` envFieldRanges env))
    value = intValue ctx facts
    -- How many elements an array that is all of its object has: a local, a
    -- global or a field, not a parameter.
    wholeArray x@(Fix inner) = case inner of
        ParenExpr y                                         -> wholeArray y
        VarExpr (L _ _ v) | Set.member v (fcParams ctx)     -> Nothing
        _ | isWhole inner, Just t <- exprType ctx x
          , [Range (Just lo) (Just hi)] <- ctDims (resolveType env t)
          , lo == hi                                        -> Just lo
        _                                                   -> Nothing
    isWhole = \case
        VarExpr{}       -> True
        MemberAccess{}  -> True
        PointerAccess{} -> True
        _               -> False
    constant v = bounded (Map.lookup v (envConstTypes env)) (Map.findWithDefault unknownRange v (envConstants env))
    -- What a function returns at most, from the arguments: a sum that is at
    -- least -1 here, as what it returns otherwise is less than 0.
    returnedAtMost f args sig =
        [ bound
        | (k, d) <- Map.toList (Map.findWithDefault Map.empty f (envAtMost env))
        , (Just param, arg) <- take 1 (drop k (zip (sigParams sig) args))
        , u <- upperForms facts (convertValue ctx facts (integerType env (paramType param)) (value arg))
        , let bound = u `linPlus` linConstant d
        , maybe False (>= -1) (lowerLin (typedFacts ctx facts bound) bound)
        ]
    -- What one of the operating system's functions the program doesn't
    -- declare returns at most ('Platform.returnsAtMost').
    systemAtMost f args =
        [ bound
        | (k, d) <- Map.toList (Platform.returnsAtMost f)
        , arg <- take 1 (drop k args)
        , u <- upperForms facts (value arg)
        , let bound = u `linPlus` linConstant d
        , maybe False (>= -1) (lowerLin (typedFacts ctx facts bound) bound)
        ]
    -- What a function returns at most, from places given to it that the
    -- call can't change.
    placedAtMost fe f args =
        [ linVar name `linPlus` linConstant d
        | (ParamPlace k steps, d) <- Map.toList (Map.findWithDefault Map.empty f (envAtMostPlaces env))
        , Fix (VarExpr (L _ _ v)) <- take 1 (drop k args)
        , unchangeable ctx v
        , Just steps' <- [argSteps (\j -> case drop j args of
                                           Fix (VarExpr (L _ _ i)) : _ | unchangeable ctx i -> Just i
                                           _ -> Nothing) steps]
        , Just name <- [placeName ctx (Path v steps')]
        , name `notElem` changedBy ctx (callEffects (fcSummaries ctx) (fcTypes ctx) (reachedVar ctx) (const Nothing) fe args)
        ]
    -- A size that isn't one number is a symbol for it.
    sizeofValue t r = case bytesLin env t of
        Just l | not (Map.null (linVars l)) -> IntValue (Just sizeType) r (Just (l, Nothing)) [] []
        _                                   -> bounded (Just sizeType) r
    -- Arithmetic on operands already in the type it's done in: what the
    -- numbers give if it doesn't wrap, else anything the type holds. A sum
    -- or difference stays one of variables, modulo the type's bits if it
    -- may have wrapped.
    arithmetic t op ia ib =
        let ra = ivRange ia
            -- What's divided by is at least what the facts say of it.
            rb | op `elem` [C.BopDiv, C.BopMod], Just l <- exactForm ib, Just lo <- lowerLin (typedFacts ctx facts l) l =
                   intersectRange (ivRange ib) (Range (Just lo) Nothing)
               | otherwise = ivRange ib
            -- Signed arithmetic past what its type holds is undefined: it's
            -- reported where it's done ('overflowFailures'), and doesn't
            -- happen.
            undefinedOverflow = op `elem` [C.BopPlus, C.BopMinus, C.BopMul] && maybe False itSigned t
            numbers = maybe id (\it -> if undefinedOverflow then intersectRange (itHolds it) else id) t (rangeArith op ra rb)
            fits r = undefinedOverflow || noWrap t op ra rb r
            anything = maybe unknownRange itCanHold t
            sumForm = do
                guard (op `elem` [C.BopPlus, C.BopMinus])
                (la, ma) <- ivForm ia
                (lb, mb) <- ivForm ib
                Just ((if op == C.BopPlus then linPlus else linMinus) la lb, ma, mb)
            -- A sum times a number is a sum, if it doesn't wrap.
            productForm = do
                guard (op == C.BopMul)
                la <- exactForm ia
                lb <- exactForm ib
                l <- case (Map.null (linVars la), Map.null (linVars lb)) of
                    (True, _) -> Just (linScale (linConst la) lb)
                    (_, True) -> Just (linScale (linConst lb) la)
                    _         -> Nothing
                guard (undefinedOverflow || maybe False (numbers `within`) (itHolds <$> t))
                return (IntValue t (rangeOfLin facts l `intersectRange` numbers) (Just (l, Nothing)) [] [])
            -- What a side is at most, moved by what the other is. What's left
            -- of a division of a number of at least 0 by a sum of at least 1
            -- is less than the sum.
            atMost
                | not (fits numbers) = []
                | op == C.BopPlus = moved linPlus ia ib ++ moved linPlus ib ia
                | op == C.BopMinus = moved linMinus ia ib
                | op == C.BopMod, maybe False (>= 0) (rLow ra), maybe False (>= 1) (rLow rb) =
                    [ l `linMinus` linConstant 1 | Just l <- [exactForm ib] ]
                | otherwise = []
            moved f ix iy = [ f u l | u <- ivAtMost ix, Just l <- [exactForm iy] ]
            value' = case (productForm, sumForm) of
                (Just iv, _) -> iv
                (_, Just (l, Nothing, Nothing))
                    | let r = rangeOfLin facts l `intersectRange` numbers
                    , fits r -> IntValue t r (Just (l, Nothing)) [] []
                (_, Just (l, ma, mb)) ->
                    let range = if fits numbers then numbers else anything
                    in IntValue t range (Just (l, Just (minimum (fewestBits t : catMaybes [ma, mb])))) [] []
                (_, Nothing) -> bounded t (if fits numbers then numbers else anything)
        in value' { ivAtMost = atMost }

-- | A value converted to an integer type: what it was if the type keeps
-- it. A sum of variables right modulo more bits than the type has, of
-- which the type holds what the numbers give, is right. A bool isn't
-- modulo anything. A value of at least 0 is at most what it was.
convertValue :: FunctionCtx Text -> Facts -> Maybe IntType -> IntValue -> IntValue
convertValue _ facts to (IntValue from r form atMost atLeast) = value
    { ivAtMost = if kept || maybe False (>= 0) (rLow r) then atMost else []
    , ivAtLeast = if kept then atLeast else []
    }
  where
    value = case form of
        Just (_, Nothing) | kept -> IntValue to r form [] []
        Just (l, m) | Just t <- to, itRank t > 0 ->
            let rl = rangeOfLin facts l
                fewerBits bits = maybe False ((<= bits) . (* 8)) (rHigh (itBytes t))
            in case m of
                Just bits | fewerBits bits, rl `within` itHolds t -> IntValue to rl (Just (l, Nothing)) [] []
                _ -> IntValue to converted (Just (l, Just (maybe id min m (fewestBits to)))) [] []
        _ -> bounded to converted
    kept = keepsValue from to r
    converted = if kept then r else maybe unknownRange itCanHold to

-- | What's known of the bounds of an integer path: what its type holds, if
-- nothing else.
pathRange :: IntType -> Text -> Facts -> Range
pathRange _ _ Unreached = unknownRange
pathRange t n facts = intersectRange (itCanHold t) (Map.findWithDefault unknownRange n (fInts facts))

-- | An integer expression as a sum of variables, if it's right.
formOf :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Maybe Lin
formOf ctx facts = exactForm . intValue ctx facts

rangeOf :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Range
rangeOf ctx facts = ivRange . intValue ctx facts

-- | An integer expression converted to a type, as a sum of variables.
convertedForm :: FunctionCtx Text -> Facts -> Maybe IntType -> C.Node (Lexeme Text) -> Maybe Lin
convertedForm ctx facts to = exactForm . convertValue ctx facts to . intValue ctx facts

-- | An integer expression converted to a type, as sums of variables it's
-- at most.
convertedUpper :: FunctionCtx Text -> Facts -> Maybe IntType -> C.Node (Lexeme Text) -> [Lin]
convertedUpper ctx facts to = upperForms facts . convertValue ctx facts to . intValue ctx facts

-- | Bounds of an integer expression converted to a type.
convertedRange :: FunctionCtx Text -> Facts -> Maybe IntType -> C.Node (Lexeme Text) -> Range
convertedRange ctx facts to = ivRange . convertValue ctx facts to . intValue ctx facts

-- | The most an integer expression converted to a type can be, if something
-- other than the types bounds it: a need made from what only the types give
-- would ask callers for more than any buffer has.
boundedMost :: FunctionCtx Text -> Facts -> Maybe IntType -> C.Node (Lexeme Text) -> Maybe Integer
boundedMost ctx facts to e = do
    most <- rHigh (convertedRange ctx facts to e)
    guard (and [ most < limit | Just t <- [ivType (intValue ctx facts e), to], Just limit <- [rHigh (itHolds t)] ])
    return most

------------------------------------------------------------------------------
-- Places
------------------------------------------------------------------------------

-- | A path the function follows, by name.
trackedPath :: FunctionCtx Text -> C.Node (Lexeme Text) -> Maybe (Text, PathInfo)
trackedPath ctx e = do
    p <- canonical ctx <$> pathOf e
    guard (not (null (pathSteps p)))
    let n = pathName p
    (,) n <$> Map.lookup n (fcPaths ctx)

-- | A place followed like a variable: a variable, or a path.
placeOf :: FunctionCtx Text -> C.Node (Lexeme Text) -> Maybe Text
placeOf ctx e = pathOf e >>= placeName ctx

placeName :: FunctionCtx Text -> Path -> Maybe Text
placeName ctx p0
    | null (pathSteps p) = Just (pathRoot p)
    | otherwise = let n = pathName p in n <$ guard (Map.member n (fcPaths ctx))
  where
    p = canonical ctx p0

-- | A path through a pointer variable that only points to one place, as a
-- path to that place.
canonical :: FunctionCtx Text -> Path -> Path
canonical ctx p = case (Map.lookup (pathRoot p) (fcAliases ctx), pathSteps p) of
    (Just place, Deref : rest) -> place { pathSteps = pathSteps place ++ rest }
    _                          -> p

-- | A name the source gives a place through a pointer to one place, as
-- the place is named.
placeNamed :: FunctionCtx Text -> Text -> Text
placeNamed ctx v = fromMaybe v $ listToMaybe
    [ pathName place <> "." <> rest
    | (p, place) <- Map.toList (fcAliases ctx)
    , Just rest <- [T.stripPrefix (p <> "->") v]
    ]

-- | A place's name as the source gives it, through a pointer to one place.
sourceNamed :: FunctionCtx Text -> Text -> Text
sourceNamed ctx v = fromMaybe v $ listToMaybe
    [ p <> "->" <> rest
    | (p, place) <- Map.toList (fcAliases ctx)
    , Just rest <- [T.stripPrefix (pathName place <> ".") v]
    ]

-- | Pointer variables declared with what a call returns, where it returns
-- the address of a place in what it's given ('envReturnsPlace'), and which
-- point there wherever they're used: nothing changes them or what the place
-- is in, or has their address.
aliasesIn :: Env -> Set.Set Text -> Set.Set Text -> C.Node (Lexeme Text) -> Map Text Path
aliasesIn env escaped params body = Map.fromList $
    -- A pointer made the address of a place, and never changed.
    [ (v, place)
    | Fix (VarDeclStmt (Fix (VarDecl _ (L _ _ v) [])) (Just (Fix (UnaryExpr C.UopAddress e)))) <- subnodes body
    , Just place <- [pathOf e]
    , not (null (pathSteps place))
    , all fixed (v : pathVars place)
    , Set.notMember v params
    , length [ () | Fix (VarDecl _ (L _ _ w) _) <- subnodes body, w == v ] == 1
    ] ++
    [ (v, Path r steps')
    | Fix (VarDeclStmt (Fix (VarDecl _ (L _ _ v) _)) (Just (Fix (FunctionCall (Fix (VarExpr (L _ _ f))) args)))) <- subnodes body
    , Just (ParamPlace k steps) <- [Map.lookup f (envReturnsPlace env)]
    , Fix (VarExpr (L _ _ r)) <- take 1 (drop k args)
    , all fixed [v, r]
    , Set.notMember v params
    , length [ () | Fix (VarDecl _ (L _ _ w) _) <- subnodes body, w == v ] == 1
    , Just steps' <- [argSteps (\j -> case drop j args of
                                       Fix (VarExpr (L _ _ i)) : _ | fixed i -> Just i
                                       _                                   -> Nothing) steps]
    ]
  where
    assigned = assignedVars body
    fixed x = Set.notMember x assigned && Set.notMember x escaped

-- | A place's elements at parameters (@#k@) at what the function names them.
argSteps :: (Int -> Maybe Text) -> [Step] -> Maybe [Step]
argSteps arg = traverse $ \case
    Index i True | Just k <- T.stripPrefix "#" i >>= readMaybe . T.unpack -> (`Index` True) <$> arg k
    Index _ True -> Nothing
    st -> Just st

-- | A place's elements at parameters, by their positions (@#k@): if all its
-- elements at variables are.
paramSteps :: Map Text Int -> [Step] -> Maybe [Step]
paramSteps params = traverse $ \case
    Index i True -> (\k -> Index ("#" <> T.pack (show k)) True) <$> Map.lookup i params
    st -> Just st

-- | What each function returning a pointer returns the address of where it
-- doesn't return nullptr: a place in what a parameter points to, at
-- elements at parameters, none of which it changes.
returnedPlaces :: [C.Node (Lexeme Text)] -> Map Text ParamPlace
returnedPlaces nodes = Map.mapMaybe id $ Map.fromListWith (\a b -> if a == b then a else Nothing)
    [ (name, place)
    | Fix (FunctionDefn _ (Fix (FunctionPrototype _ (L _ _ name) params)) body) <- concatMap subnodes nodes
    , let names = Map.fromList (zip [ p | Fix (VarDecl _ (L _ _ p) _) <- params ] [0 ..])
          changed = assignedVars body
          returned e = case unFix e of
              ParenExpr x -> returned x
              _ | isNullptr e -> Just Nothing
              UnaryExpr C.UopAddress x -> do
                  Path r steps <- pathOf x
                  guard (all (`Set.notMember` changed) (r : [ i | Index i True <- steps ]))
                  k <- Map.lookup r names
                  Just . ParamPlace k <$> paramSteps names steps
              _ -> Nothing
          place = do
              places <- catMaybes <$> traverse returned [ e | Fix (Return (Just e)) <- subnodes body ]
              case places of
                  p : ps | all (== p) ps -> Just p
                  _                      -> Nothing
    ]

typeOfPlace :: FunctionCtx Text -> Text -> Maybe CType
typeOfPlace ctx v = resolveType (fcEnv ctx) <$> case Map.lookup v (fcPaths ctx) of
    Just info -> piType info
    Nothing   -> Map.lookup v (fcTypes ctx)

-- | Paths whose place depends on a variable: those from it, and those with
-- it as an index.
pathsWith :: FunctionCtx Text -> Text -> [Text]
pathsWith ctx v = Map.findWithDefault [] v (ixWith (fcIndex ctx))

pairsTouching :: FunctionCtx Text -> [Text] -> [Pair]
pairsTouching ctx ns = nub (concatMap (\n -> Map.findWithDefault [] n (ixPairsOf (fcIndex ctx))) ns)

isPairMember :: FunctionCtx Text -> Text -> Bool
isPairMember ctx n = Map.member n (ixPairsOf (fcIndex ctx))

-- | Forgets places outright.
forgetPlaces :: [Text] -> Facts -> Facts
forgetPlaces ns facts = foldl' (flip forgetVar) facts ns

-- | What's known of the bounds of a place: for an integer path, what its
-- type holds if nothing else.
placeRange :: FunctionCtx Text -> Text -> Facts -> Range
placeRange ctx v facts = case Map.lookup v (fcPaths ctx) >>= piType >>= integerType (fcEnv ctx) of
    Just t  -> pathRange t v facts
    Nothing -> case facts of
        Unreached -> unknownRange
        _         -> Map.findWithDefault unknownRange v (fInts facts)

-- | A place with its bounds written down, for what's worked out from them.
withRange :: FunctionCtx Text -> Text -> Facts -> Facts
withRange ctx v facts = setRange v (placeRange ctx v facts) facts

-- | Forgets paths something else may have changed. A pair they're in still
-- holds: it's checked wherever it changes.
forgetPaths :: FunctionCtx Text -> [Text] -> Facts -> Facts
forgetPaths ctx ns = trust (`elem` ns) (pairsTouching ctx ns) . forgetPlaces ns

-- | A pair's buffer has as many elements as its length says, and its count
-- is at most that. What's known of a length or count that didn't change
-- stays.
trust :: (Text -> Bool) -> [Pair] -> Facts -> Facts
trust changed prs facts = foldl' one facts prs
  where
    one fs pr =
        let len = prLength pr
            forget v = if changed v then forgetVar v else id
            fs' = forgetVar (prBuffer pr) (forget len (foldr forget fs (prCount pr)))
            known = case fs' of
                Unreached -> unknownRange
                Facts{}   -> Map.findWithDefault unknownRange len (fInts fs')
            holds = intersectRange known (maybe unknownRange itCanHold (prLengthType pr))
            counted gs = foldr (\c -> addIneq (linVar len `linMinus` linVar c) . withinType c) gs (prCount pr)
            withinType v gs = case gs of
                Unreached -> Unreached
                Facts{}   -> setRange v (intersectRange (Map.findWithDefault unknownRange v (fInts gs)) (maybe unknownRange itCanHold (prCountType pr))) gs
        in counted $ case prElements pr of
            Just n  -> setRange len (intersectRange holds (Range Nothing (Just n))) fs'
            Nothing -> setNewPointer (prBuffer pr) (prBuffer pr <> "#") (Size (linVar len)) (setRange len holds fs')

-- | What a pointer may have as many elements as after a join: a buffer
-- field's length field.
sizeHints :: FunctionCtx Text -> Text -> [Lin]
sizeHints ctx p = [ linVar (prLength pr) | pr <- fcPairs ctx, prBuffer pr == p, isNothing (prElements pr) ]

-- | Where the pointers and addresses an argument is made from point.
pointsInto :: FunctionCtx Text -> C.Node (Lexeme Text) -> [(Path, Bool)]
pointsInto ctx (Fix node) = case node of
    ParenExpr e                -> pointsInto ctx e
    CastExpr _ e               -> pointsInto ctx e
    BinaryExpr a op b
        | op `elem` [C.BopPlus, C.BopMinus] -> pointsInto ctx a ++ pointsInto ctx b
    TernaryExpr _ a b          -> pointsInto ctx a ++ pointsInto ctx b
    UnaryExpr C.UopAddress x   -> [ (canonical ctx p, True) | Just p <- [pathOf x] ]
    -- A pointer to one place is that place's address.
    VarExpr (L _ _ v) | Just place <- Map.lookup v (fcAliases ctx) -> [(place, True)]
    _                          -> [ (canonical ctx p, False) | Just p <- [pathOf (Fix node)] ]

type Call = (C.Node (Lexeme Text), [C.Node (Lexeme Text)])

-- | The calls among a statement's expressions.
callsIn :: [C.Node (Lexeme Text)] -> [Call]
callsIn exprs = [ (f, args) | Fix (FunctionCall f args) <- exprs, not (isAssume f) ]

-- | Paths the calls in a statement may change: those in memory their
-- arguments point to, and those from variables any code may have the
-- address of.
callsReach :: FunctionCtx Text -> [Call] -> [Text]
callsReach ctx = nub . concatMap (callReach ctx)

-- | Whether a variable is the function's own, and nothing it calls can
-- change it.
unchangeable :: FunctionCtx Text -> Text -> Bool
unchangeable ctx v = Map.member v (fcTypes ctx) && not (reachedVar ctx v)

-- | Whether something else than the function can reach a variable: one a
-- call or a store through a pointer may change, an array's elements too,
-- and what a parameter written as an array points to.
reachedVar :: FunctionCtx Text -> Text -> Bool
reachedVar ctx v = Set.member v (fcEscaped ctx)
    || Set.member v (fcParams ctx) && maybe False (not . null . ctDims . resolveType (fcEnv ctx)) (Map.lookup v (fcTypes ctx))

-- | Paths stores may change.
changedBy :: FunctionCtx Text -> Effects -> [Text]
changedBy ctx effects = [ n | (n, info) <- Map.toList (fcPaths ctx), mayChange (fcSummaries ctx) effects (piFoot info) ]

-- | Paths one call may change.
callReach :: FunctionCtx Text -> Call -> [Text]
callReach ctx (_, args) = nub $ ixEscaped (fcIndex ctx) ++
    [ n
    | (p, address) <- concatMap (pointsInto ctx) args
    , (n, q) <- Map.findWithDefault [] (pathRoot p) (ixByRoot (fcIndex ctx))
    , if address then q `isPartOf` p else q `isThrough` p
    ]

-- | Pair members a call is given a pointer to, which it may change to
-- anything: through an address, or a pointer to it.
writtenThrough :: FunctionCtx Text -> [Call] -> [Text]
writtenThrough ctx calls =
    [ n
    | (_, args) <- calls
    , (p, address) <- concatMap (pointsInto ctx) args
    , Just n <- [placeName ctx (if address then p else p { pathSteps = pathSteps p ++ [Deref] })]
    , isPairMember ctx n
    ]

-- | A statement of what holds, which is no call: the CFG's for a branch,
-- or an assert.
isAssume :: C.Node (Lexeme Text) -> Bool
isAssume (Fix (VarExpr (L _ _ f))) = "__tokstyle_" `T.isPrefixOf` f || f == "assert"
isAssume _                         = False

------------------------------------------------------------------------------
-- Transfer
------------------------------------------------------------------------------

transferStmt :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Facts
transferStmt _ Unreached _ = Unreached
transferStmt ctx facts stmt@(Fix node) = case node of
    ExprStmt (Fix (FunctionCall (Fix (VarExpr (L _ _ "__tokstyle_assume_true"))) [cond])) ->
        narrow ctx True cond facts
    ExprStmt (Fix (FunctionCall (Fix (VarExpr (L _ _ "__tokstyle_assume_false"))) [cond])) ->
        narrow ctx False cond facts
    -- What an assert says holds after it: where it can't be shown, that's
    -- reported ('assertFailures').
    ExprStmt (Fix (FunctionCall (Fix (VarExpr (L _ _ "assert"))) [cond])) ->
        narrow ctx True cond (transferStmt ctx facts (Fix (ExprStmt cond)))
    VLA _ (L _ _ name) size ->
        let facts' = changed
        in case lengthSize ctx facts' size of
            Just sz -> setNewPointer name (arrayOrigin name) sz facts'
            Nothing -> forgetVar name facts'
    VarDeclStmt d mInit -> case declType (fcEnv ctx) d of
        Just (name, ty) -> zeroed (sized d name (declare ctx name ty mInit (fresh name mInit (forgetVar name changed))))
        Nothing         -> changed
    _ -> changed
  where
    -- What its calls may have changed, then what the statement assigns,
    -- then what its calls and stores through pointers may have changed of
    -- variables, and what out-parameters were given.
    exprs = statementExprs stmt
    calls = callsIn exprs
    effectsOf (f, args) = callEffects (fcSummaries ctx) (fcTypes ctx) (reachedVar ctx) (const Nothing) f args
    effects = foldMap effectsOf calls
    -- A call that may do anything changes the function's own arrays it's
    -- given.
    ownGiven = [ v | call@(_, args) <- calls, Anything <- [effectsOf call], a <- args, Just v <- [ownArrayIn (fcEnv ctx) (fcTypes ctx) (reachedVar ctx) a] ]
    called = leftBy (forgetPlaces (writtenThrough ctx calls) (forgetPaths ctx (changedBy ctx effects ++ concatMap (pathsWith ctx) ownGiven) facts))
    -- What a call that is the statement leaves places it's given at.
    leftBy fs = case statementCall of
        Just (f, args) -> foldl' (leaveAt args) fs (Map.toList (Map.findWithDefault Map.empty f (envLeaves (fcEnv ctx))))
        Nothing -> fs
    statementCall = case unFix stmt of
        ExprStmt e             -> callOf e
        VarDeclStmt _ (Just e) -> callOf e
        _                      -> Nothing
    callOf (Fix e) = case e of
        ParenExpr x                                 -> callOf x
        CastExpr _ x                                -> callOf x
        AssignExpr _ C.AopEq x                      -> callOf x
        FunctionCall (Fix (VarExpr (L _ _ f))) args -> Just (f, args)
        _                                           -> Nothing
    leaveAt args fs (ParamPlace k steps, r) = fromMaybe fs $ do
        steps' <- argSteps (\j -> case drop j args of
                                    Fix (VarExpr (L _ _ i)) : _ | unchangeable ctx i -> Just i
                                    _ -> Nothing) steps
        path <- case drop k args of
            Fix (VarExpr (L _ _ v)) : _ | unchangeable ctx v -> Just (Path v steps')
            Fix (UnaryExpr C.UopAddress (Fix (VarExpr (L _ _ v)))) : _ | Deref : rest <- steps' -> Just (Path v rest)
            _ -> Nothing
        name <- placeName ctx path
        return (setRange name (intersectRange r (placeRange ctx name fs)) fs)
    assigned = assignments ctx (givenBack ctx facts calls exprs (addressTaken ctx taken called)) stmt
    -- A pointer made a place's address, which is followed as that place
    -- ('fcAliases'), doesn't give it away.
    taken = case unFix stmt of
        VarDeclStmt (Fix (VarDecl _ (L _ _ v) [])) _ | Map.member v (fcAliases ctx) -> []
        _ -> exprs
    stored
        | not (null calls) = foldl' (flip forgetVar) assigned
            [ v | v <- Set.toList (fcEscaped ctx), mayChange (fcSummaries ctx) effects (footprint (fcEnv ctx) (fcTypes ctx) (reachedVar ctx) (Path v [])) ]
        | otherwise = foldl' (flip forgetVar) assigned (filter (storedTo ctx exprs) (Set.toList (fcEscaped ctx)))
    changed = assignedZeros (givenOut ctx calls stored)
    -- What a function that gives back memory all zeros gives is in one
    -- object: its numbers start at 0.
    zeroed fs = case unFix stmt of
        VarDeclStmt (Fix (VarDecl _ (L _ _ v) [])) (Just rhs) | fromZeroed rhs -> zeros v fs
        _ -> fs
    assignedZeros fs = case unFix stmt of
        ExprStmt (Fix (AssignExpr (Fix (VarExpr (L _ _ v))) C.AopEq rhs)) | fromZeroed rhs -> zeros v fs
        ExprStmt (Fix (AssignExpr lhs C.AopEq rhs)) | zeroConstant rhs, Just p <- pathOf lhs -> zerosIn (canonical ctx p) fs
        _ -> fs
    zeroConstant (Fix e) = case e of
        ParenExpr x       -> zeroConstant x
        VarExpr (L _ _ c) -> Set.member c (envZeroConsts (fcEnv ctx))
        _                 -> False
    -- A struct given zeros: its numbers, in it and the structs in it, are 0.
    zerosIn p fs = foldl' (\acc n -> setRange n (exactly 0) acc) fs
        [ n
        | (n, info) <- Map.toList (fcPaths ctx)
        , let q = piPath info
        , q `isPartOf` p
        , Deref `notElem` drop (length (pathSteps p)) (pathSteps q)
        , isJust (piType info >>= integerType (fcEnv ctx))
        ]
    fromZeroed (Fix e) = case e of
        ParenExpr x -> fromZeroed x
        CastExpr _ x -> fromZeroed x
        FunctionCall (Fix (VarExpr (L _ _ f))) _ -> Set.member f (envZeroed (fcEnv ctx))
        _ -> False
    zeros v fs = foldl' (\acc n -> setRange n (exactly 0) acc) fs
        [ n
        | (n, info) <- Map.toList (fcPaths ctx)
        , Path root (Deref : rest) <- [piPath info]
        , root == v
        , Deref `notElem` rest
        , isJust (piType info >>= integerType (fcEnv ctx))
        ]
    -- An array as long as a sum of the sizes of types has that many
    -- elements, whatever the sizes are.
    sized (Fix (VarDecl _ _ (Fix (DeclSpecArray _ (Just dim)) : _))) name fs
        | Just l <- formOf ctx fs dim, not (Map.null (linVars l)) = setNewPointer name (arrayOrigin name) (Size l) fs
    sized _ _ fs = fs
    -- A new variable's paths: a pair holds in it, but not in what an
    -- initialiser gives it.
    fresh name mInit fs =
        let ps = pathsWith ctx name
        in if maybe True given mInit
           then forgetPaths ctx ps fs
           else forgetPlaces (ps ++ concat [ [prBuffer pr, prLength pr] | pr <- pairsTouching ctx ps ]) fs
    given (Fix (InitialiserList es)) = all isZero es
    given _                          = True
    isZero (Fix e) = case e of
        InitialiserList es                      -> all isZero es
        LiteralExpr C.Int (L _ _ "0")           -> True
        LiteralExpr C.ConstId (L _ _ "nullptr") -> True
        LiteralExpr C.ConstId (L _ _ "false")   -> True
        _                                       -> False

-- | Whether a store in a statement may change a variable whose address is
-- taken: through a pointer to something of its size or type that isn't
-- given its own value.
storedTo :: FunctionCtx Text -> [C.Node (Lexeme Text)] -> Text -> Bool
storedTo ctx exprs v = any writes exprs
  where
    env = fcEnv ctx
    varType = resolveType env <$> Map.lookup v (fcTypes ctx)
    writes (Fix node) = case node of
        AssignExpr (Fix VarExpr{}) _ _ -> False
        AssignExpr lhs op rhs          -> mayAlias lhs && not (op == C.AopEq && isItself rhs)
        UnaryExpr o x | o `elem` [C.UopIncr, C.UopDecr] -> case x of
            Fix VarExpr{} -> False
            _             -> mayAlias x
        _ -> False
    isItself (Fix e) = case e of
        ParenExpr x       -> isItself x
        VarExpr (L _ _ w) -> w == v
        _                 -> False
    mayAlias lhs = case (resolveType env <$> exprType ctx lhs, varType) of
        (Just t, Just u)
            | t == u -> True
            | Just a <- integerType env t, Just b <- integerType env u -> itBytes a == itBytes b
            | isPointerType t /= isPointerType u -> False
            | isStruct t || isStruct u -> False
        _ -> True
    isStruct t = ctPointers t == 0 && null (ctDims t) && Map.member (ctName t) (envStructs env)

-- | The size of a buffer with as many elements as an integer expression.
lengthSize :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Maybe Size
lengthSize ctx facts e = case formOf ctx facts e of
    Just l  -> Just (Size l)
    Nothing -> elements <$> rLow (rangeOf ctx facts e)

-- | A place whose address is taken may change wherever it goes. A pair's
-- buffer or length is then whatever it's given.
addressTaken :: FunctionCtx Text -> [C.Node (Lexeme Text)] -> Facts -> Facts
addressTaken ctx exprs facts = foldl' forget facts [ canonical ctx p | Fix (UnaryExpr C.UopAddress x) <- exprs, Just p <- [pathOf x] ]
  where
    forget fs p = case placeName ctx p of
        Just v | null (pathSteps p) -> forgetPaths ctx (pathsWith ctx v) (forgetVar v fs)
        Just v -> forgetPlaces [v] (forgetPaths ctx [ n | n <- partsOf p, n /= v ] fs)
        Nothing -> forgetPaths ctx (partsOf p) fs
    partsOf p = [ n | (n, q) <- Map.findWithDefault [] (pathRoot p) (ixByRoot (fcIndex ctx)), q `isPartOf` p ]

-- | Out-parameters for a buffer and its length are given a buffer with that
-- many elements.
givenOut :: FunctionCtx Text -> [Call] -> Facts -> Facts
givenOut ctx calls facts = foldl' give facts
    [ (buf, len)
    | (f, args) <- calls
    , Just (_, sig) <- [signatureOf ctx f]
    , (i, Just param) <- zip [0 :: Int ..] (sigParams sig)
    , Just j <- [paramOutLength param]
    , Just buf <- [lookup i (zip [0 ..] args) >>= outTarget ctx]
    , Just len <- [lookup j (zip [0 ..] args) >>= outTarget ctx]
    ]
  where
    give fs (buf, len) = setNewPointer buf (buf <> "#out") (Size (linVar len)) (forgetPlaces [buf, len] fs)

-- | The place a pointer given to a call points to.
outTarget :: FunctionCtx Text -> C.Node (Lexeme Text) -> Maybe Text
outTarget ctx arg = case unFix arg of
    ParenExpr x              -> outTarget ctx x
    UnaryExpr C.UopAddress x -> placeOf ctx x
    _                        -> pathOf arg >>= \p -> placeName ctx p { pathSteps = pathSteps p ++ [Deref] }

declare :: FunctionCtx Text -> Text -> CType -> Maybe (C.Node (Lexeme Text)) -> Facts -> Facts
declare ctx name ty mInit facts = case mInit of
    Nothing -> facts
    Just e
        | isPointerType ty && null (ctDims ty) -> assignPointer ctx name e facts
        | isIntegerType (fcEnv ctx) ty -> setInt ctx name ty e facts
        | otherwise -> facts

-- | A pointer variable given a value: into the same buffer if it's a place
-- in one, else at a new origin with what's known of its size.
assignPointer :: FunctionCtx Text -> Text -> C.Node (Lexeme Text) -> Facts -> Facts
assignPointer ctx p e facts = case cursorOf ctx facts e of
    Just (o, off, base) -> setPointer p o off base facts
    Nothing -> case sizeOf ctx facts e of
        Just sz -> setNewPointer p (newOrigin p e) sz facts
        Nothing -> forgetVar p facts

-- | An origin for a buffer a pointer is given at a place in the code.
newOrigin :: Text -> C.Node (Lexeme Text) -> Text
newOrigin p e = p <> "#" <> maybe "" (\(C.AlexPn o _ _) -> T.pack (show o)) (getAlexPosn e)

-- | An integer variable given a value: what's known of the value holds only
-- if the variable's type keeps it, else the sums it's at most do
-- ('upperForms').
setInt :: FunctionCtx Text -> Text -> CType -> C.Node (Lexeme Text) -> Facts -> Facts
setInt ctx v ty e facts = returned (unlessNone ctx v ty e facts (givenNone ctx v ty e facts (setIntValue ctx v ty e facts)))
  where
    returned fs = foldl' (\gs u -> addIneq (u `linMinus` linVar v) gs) fs
        [ u | (u, rt) <- placesReturnedAtMost ctx e, rt == integerType (fcEnv ctx) ty, isJust rt ]

-- | Sums of places given to a call (or to each of a choice of calls) that
-- what it returns is at most ('envAtMostPlaces'), as they are once it has
-- returned, whether it changed them or not; with the type it returns.
placesReturnedAtMost :: FunctionCtx Text -> C.Node (Lexeme Text) -> [(Lin, Maybe IntType)]
placesReturnedAtMost ctx (Fix e) = case e of
    ParenExpr x -> placesReturnedAtMost ctx x
    TernaryExpr _ a b -> let as = placesReturnedAtMost ctx a in filter (`elem` as) (placesReturnedAtMost ctx b)
    FunctionCall (Fix (VarExpr (L _ _ f))) args | Just sig <- Map.lookup f (envFunctions env) ->
        [ (linVar name `linPlus` linConstant d, integerType env (sigReturn sig))
        | (ParamPlace k steps, d) <- Map.toList (Map.findWithDefault Map.empty f (envAtMostPlaces env))
        , Fix (VarExpr (L _ _ v)) <- take 1 (drop k args)
        , unchangeable ctx v
        , Just steps' <- [argSteps (\j -> case drop j args of
                                           Fix (VarExpr (L _ _ i)) : _ | unchangeable ctx i -> Just i
                                           _ -> Nothing) steps]
        , Just name <- [placeName ctx (Path v steps')]
        ]
    _ -> []
  where
    env = fcEnv ctx

-- | An unsigned variable given the most its type holds, which stands for
-- none, has its 'noneVar' 1; one that had one, given less, has it 0, and
-- given what may be either, may be either.
givenNone :: FunctionCtx Text -> Text -> CType -> C.Node (Lexeme Text) -> Facts -> Facts -> Facts
givenNone ctx v ty e before after = case integerType (fcEnv ctx) ty of
    Just t | Set.member v (fcCompared ctx), not (itSigned t), Just k <- rHigh (itHolds t) ->
        let r = ivRange (convertValue ctx before (Just t) (intValue ctx before e))
            z = noneVar v k
            linked zr = foldl' (flip addIneq) (setRange z zr (forgetInt z after))
                [ linVar v `linMinus` linScale k (linVar z)
                , linConstant (k - 1) `linPlus` linVar z `linMinus` linVar v ]
        in if r == exactly k then linked (exactly 1)
           else if not (had z) then after
           else if maybe False (< k) (rHigh r) then linked (exactly 0)
           else linked (Range (Just 0) (Just 1))
    _ -> after
  where
    had z = case before of
        Facts{fInts = is} -> Map.member z is
        Unreached         -> False

-- | Variables a function compares with a constant by @==@ or @!=@.
comparedWithConstants :: C.Node (Lexeme Text) -> Set.Set Text
comparedWithConstants body = Set.fromList
    [ v
    | Fix (BinaryExpr a op b) <- subnodes body
    , op `elem` [C.BopEq, C.BopNe]
    , (Fix (VarExpr (L _ _ v)), Fix LiteralExpr{}) <- [(a, b), (b, a)]
    ]

-- | A variable given what a call returns that's at most sums of what it's
-- given unless it's a number for none ('envAtMostUnless'): z, 1 where the
-- variable is that number, else 0, has v >= k * z, v <= k - 1 + z, and
-- v <= u + (k + 1) * z for each sum u of at least -1. Where v is found not
-- to be k, z is 0, and v is at most each sum. What v changes to moves or
-- drops these with it.
unlessNone :: FunctionCtx Text -> Text -> CType -> C.Node (Lexeme Text) -> Facts -> Facts -> Facts
unlessNone ctx v ty e before after = case e of
    Fix (FunctionCall (Fix (VarExpr (L _ _ f))) args)
        | Just (k, most) <- Map.lookup f (envAtMostUnless env)
        , Just sig <- Map.lookup f (envFunctions env)
        , Just t <- integerType env (sigReturn sig)
        , integerType env ty == Just t
        , let z = noneVar v k
        , let us = [ u `linPlus` linConstant d
                   | (j, d) <- Map.toList most
                   , (Just param, arg) <- take 1 (drop j (zip (sigParams sig) args))
                   , u <- upperForms before (convertValue ctx before (integerType env (paramType param)) (intValue ctx before arg))
                   , not (linMentions v u)
                   , maybe False (>= -1) (lowerLin before (u `linPlus` linConstant d))
                   ]
        , not (null us) ->
            let linked = foldl' (flip addIneq) (setRange z (Range (Just 0) (Just 1)) (forgetInt z after))
                    [ linVar v `linMinus` linScale k (linVar z)
                    , linConstant (k - 1) `linPlus` linVar z `linMinus` linVar v ]
            in foldl' (\fs u -> addIneq (u `linMinus` linVar v `linPlus` linScale (k + 1) (linVar z)) fs) linked us
    _ -> after
  where
    env = fcEnv ctx

setIntValue :: FunctionCtx Text -> Text -> CType -> C.Node (Lexeme Text) -> Facts -> Facts
setIntValue ctx v ty e facts =
    let iv = convertValue ctx facts (integerType (fcEnv ctx) ty) (intValue ctx facts e)
        r = ivRange iv
    in case exactForm iv of
        -- The places it's the same as keep their bounds where it's linked.
        Just l | not (linMentions v l) ->
            let known = foldl' (\acc w -> if Map.member w (fcPaths ctx) then withRange ctx w acc else acc) facts (Map.keys (linVars l))
                fs = setIntLin v l known
            in setRange v (intersectRange r (placeRange ctx v fs)) fs
        _ -> foldl' (flip addIneq) (setRange v r facts)
                 ([ l `linMinus` linVar v | l <- upperForms facts iv, not (linMentions v l) ]
                  ++ [ linVar v `linMinus` l | l <- ivAtLeast iv, not (linMentions v l) ])

-- | The assignments in a statement, in order.
assignments :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> Facts
assignments ctx facts0 stmt = foldl' apply facts0 (collect stmt)
  where
    collect (Fix node) = case node of
        AssignExpr lhs op rhs -> collect rhs ++ [Left (lhs, op, rhs)]
        UnaryExpr C.UopIncr x -> collect x ++ [Right (x, 1)]
        UnaryExpr C.UopDecr x -> collect x ++ [Right (x, -1)]
        -- Statements inside are their own CFG nodes.
        IfStmt c _ _          -> collect c
        WhileStmt c _         -> collect c
        DoWhileStmt _ c       -> collect c
        ForStmt i _ _ _       -> collect i
        SwitchStmt c _        -> collect c
        CompoundStmt _        -> []
        _                     -> concatMap collect (toList node)
    typeOfVar = typeOfPlace ctx
    apply before = \case
        Left (lhs, op, rhs) -> case placeOf ctx lhs of
            Nothing -> unknownStore lhs before
            Just v -> let facts = beforeStore v before in case (typeOfVar v, op) of
                (Just ty, C.AopEq)
                    | isPointerType ty -> assignPointer ctx v rhs facts
                    | Just (op', e) <- selfMove facts v rhs -> apply before (Left (lhs, op', e))
                    | otherwise        -> setInt ctx v ty rhs (forgetInt v facts)
                (Just ty, C.AopPlus)
                    | isPointerType ty -> movePointer v (formOf ctx facts rhs) (rangeOf ctx facts rhs) facts
                    | Just l <- formOf ctx facts rhs, not (linMentions v l) -> moveIntFitting v ty (ivType (intValue ctx facts rhs)) l facts
                (Just ty, C.AopMinus)
                    | not (isPointerType ty), Just l <- formOf ctx facts rhs, not (linMentions v l) ->
                        moveIntFitting v ty (ivType (intValue ctx facts rhs)) (linScale (-1) l) facts
                _ -> forgetVar v facts
        Right (x, k) -> case placeOf ctx x of
            Nothing -> unknownStore x before
            Just v -> let facts = beforeStore v before in case typeOfVar v of
                Just ty
                    | isPointerType ty -> if k > 0 then movePointer v (Just (linConstant k)) (exactly k) facts else forgetVar v facts
                    | otherwise        -> moveIntFitting v ty (Just intType) (linConstant k) facts
                Nothing -> forgetVar v facts
    -- v = v + e and v = v - e are v += e and v -= e: C works both out in the
    -- same type and converts back the same way.
    selfMove fs v (Fix (ParenExpr e)) = selfMove fs v e
    selfMove fs v (Fix (BinaryExpr a op b))
        | placeOf ctx a == Just v, op == C.BopPlus, keeps b  = Just (C.AopPlus, b)
        | placeOf ctx a == Just v, op == C.BopMinus, keeps b = Just (C.AopMinus, b)
        | placeOf ctx b == Just v, op == C.BopPlus, keeps a  = Just (C.AopPlus, a)
      where keeps e = maybe False (not . linMentions v) (formOf ctx fs e)
    selfMove _ _ _ = Nothing
    -- A variable given a value moves the paths from it. A path given one
    -- may be what others with its last step are, but for those in another
    -- variable when both are in their variables' own memory, and moves the
    -- paths from it; a pair in another stays as it is, and is checked where
    -- it is.
    beforeStore v fs = case Map.lookup v (fcPaths ctx) of
        Nothing -> forgetPaths ctx (pathsWith ctx v) fs
        Just info ->
            let p = piPath info
                lastStep = take 1 (reverse (pathSteps p))
                apart q = pathRoot q /= pathRoot p && inOwnMemory ctx p && inOwnMemory ctx q
                aliases = [ i | (n, i) <- Map.toList (fcPaths ctx), n /= v
                              , take 1 (reverse (pathSteps (piPath i))) == lastStep, piType i == piType info
                              , not (apart (piPath i)) ]
                from q = [ n | (n, i) <- Map.toList (fcPaths ctx), piPath i `isPartOf` piPath q, n /= pathName (piPath q) ]
            in forgetPaths ctx (concatMap from (info : aliases))
                (forgetPlaces [ n | i <- aliases, let n = pathName (piPath i), not (isPairMember ctx n) ] fs)
    -- A store through a pointer may change any path of its type, but not a
    -- pair: only a path, or what its address was given to, changes those.
    -- One in a variable's own memory changes only paths in that variable.
    unknownStore lhs fs =
        let t = resolveType (fcEnv ctx) <$> exprType ctx lhs
            inside = [ pathRoot q | Just q <- [pathOf lhs], inOwnMemory ctx q ]
            mayBe i = fromMaybe True ((==) <$> t <*> piType i) && all (== pathRoot (piPath i)) inside
        in forgetPlaces [ n | (n, i) <- Map.toList (fcPaths ctx), mayBe i, not (isPairMember ctx n) ] fs
    -- A pointer moved forward within its buffer: by a sum, its offset moves;
    -- by an amount of which only the bounds are known, it starts again at a
    -- new origin with what's left.
    movePointer p mForm r fs = case Map.lookup p (pointersOf fs) of
        Nothing
            | Just sz <- typeOfVar p >>= arrayElements ->
                movePointer p mForm r (setNewPointer p (arrayOrigin p) sz fs)
            | otherwise -> forgetVar p fs
        Just _ -> case mForm of
            Just l | not (linMentions (offsetVar p) l), let fs' = ranged l fs, maybe False (>= 0) (rLow (rangeOfLin fs' l)) ->
                moveInt (offsetVar p) l fs'
            _ -> case sizeOf ctx fs (var p) >>= advance r of
                Just sz -> setNewPointer p (p <> "#moved") sz fs
                Nothing -> forgetVar p fs
    -- Moved past what its type holds, a variable wraps: nothing is known,
    -- but that an unsigned one moved up by a number is at most what it was
    -- (named for it, with all that's known of it) and that number. As
    -- v - (-l), it can't have passed the end it moved away from. Signed
    -- arithmetic in the variable's own type doesn't go past it: that's
    -- undefined, and reported where it's done.
    moveIntFitting v ty other l fs0 =
        let fs = ranged l (withRange ctx v fs0)
            moved0 = moveInt v l fs
            -- What the sum is, from what's known of how they relate.
            exact = rangeOfLin fs (linVar v `linPlus` l)
            moved = setRange v (intersectRange exact (Map.findWithDefault unknownRange v (intsOf moved0))) moved0
            old = Map.findWithDefault unknownRange v (intsOf fs)
            new = Map.findWithDefault unknownRange v (intsOf moved)
            back = rangeOfLin fs (linScale (-1) l)
            t = integerType (fcEnv ctx) ty
        in if noWrap t C.BopMinus old back new then moved
           else case t of
               Just it | undefinedIn it other -> setRange v (intersectRange (itHolds it) new) moved
               Just it | not (itSigned it), Map.null (linVars l), linConst l > 0 ->
                   let before = v <> "#before"
                       kept = forgetInt v (setIntLin before (linVar v) (forgetInt before fs))
                   in addIneq (linVar before `linPlus` l `linMinus` linVar v)
                       (setRange v (Range (Just 0) (rHigh (intersectRange (itCanHold it) new))) kept)
               _                              -> forgetInt v fs0
    -- A variable nothing else is known of, as one given to an
    -- out-parameter, holds what its type can.
    ranged l fs = foldl' typeRange fs (Map.keys (linVars l))
    typeRange fs v = case typeOfVar v >>= integerType (fcEnv ctx) of
        Just t | Map.notMember v (intsOf fs) -> setRange v (itCanHold t) fs
        _                                    -> fs
    pointersOf Unreached = Map.empty
    pointersOf fs        = fPointers fs
    intsOf Unreached = Map.empty
    intsOf fs        = fInts fs
    var p = Fix (VarExpr (L (C.AlexPn 0 0 0) C.IdVar p))

-- | Whether arithmetic on a variable of a type and a value of another (if
-- known) is done in the variable's type, and that's signed: going past
-- what it holds is undefined.
undefinedIn :: IntType -> Maybe IntType -> Bool
undefinedIn t other = itSigned t && promote t == t && maybe False (\o -> commonType t (promote o) == t) other

-- | What a branch tells about integer variables.
narrow :: FunctionCtx Text -> Bool -> C.Node (Lexeme Text) -> Facts -> Facts
narrow _ _ _ Unreached   = Unreached
narrow ctx truth e facts = madeBy ctx truth e (narrowed ctx truth e facts)

-- | Where a condition says a call did what it was asked, the buffers it
-- made have as many elements as it says ('envMadeSizes'), what it made
-- sure of holds ('envMadeSums'), and what it stored through pointers is
-- what it says ('envMadeStores'): in the caller's terms, where the call
-- can't have changed them.
madeBy :: FunctionCtx Text -> Bool -> C.Node (Lexeme Text) -> Facts -> Facts
madeBy _ _ _ Unreached = Unreached
madeBy ctx truth (Fix node) facts = case node of
    FunctionCall fe@(Fix (VarExpr (L _ _ f))) args
        | Just sig <- Map.lookup f (envFunctions env)
        , if resolveType env (sigReturn sig) == CType "bool" 0 [] then truth else not truth && isJust (integerType env (sigReturn sig)) ->
            made fe f sig args
    BinaryExpr a op b
        | Just cmp <- comparison op
        , let cmp' = if truth then cmp else negateCmp cmp
        , Just (fe, f, args, c, cmp'') <- case (a, b) of
            (Fix (FunctionCall fe@(Fix (VarExpr (L _ _ f))) args), _) | Just c <- number b -> Just (fe, f, args, c, cmp')
            (_, Fix (FunctionCall fe@(Fix (VarExpr (L _ _ f))) args)) | Just c <- number a -> Just (fe, f, args, c, flipCmp cmp')
            _ -> Nothing
        , Just sig <- Map.lookup f (envFunctions env)
        , Just (Range (Just lo) (Just hi)) <- Map.lookup f (envIntReturns env)
        , hi - lo <= 64
        , [0] <- filter (\v -> holdsCmp cmp'' v c) [lo .. hi] ->
            made fe f sig args
    _ -> facts
  where
    env = fcEnv ctx
    number x = case rangeOf ctx facts x of
        Range (Just lo) (Just hi) | lo == hi -> Just lo
        _                                    -> Nothing
    holdsCmp cmp v c = case cmp of
        CLt -> v < c
        CLe -> v <= c
        CGt -> v > c
        CGe -> v >= c
        CEq -> v == c
        CNe -> v /= c
    made fe f sig args =
        let changed = changedBy ctx (callEffects (fcSummaries ctx) (fcTypes ctx) (reachedVar ctx) (const Nothing) fe args)
            untouched w = if Map.member w (fcTypes ctx) then unchangeable ctx w else w `notElem` changed
            sized' = foldl' (sized fe untouched sig args) facts (Map.toList (Map.findWithDefault Map.empty f (envMadeSizes env)))
            stored' = foldl' (storedIn args) sized' (Map.toList (Map.findWithDefault Map.empty f (envMadeStores env)))
        in foldl' (summed untouched sig args) stored' (Map.findWithDefault [] f (envMadeSums env))
    fixedArg args j = case drop j args of
        Fix (VarExpr (L _ _ i)) : _ | unchangeable ctx i -> Just i
        _                                                -> Nothing
    -- A sum of what's given, put in the caller's terms where they're the
    -- untouched after the call as what the function was given: an integer
    -- argument of variables the call can't change, or what fields and
    -- pointers lead to from such a variable.
    summed untouched sig args fs (g, b) = case traverse (term untouched sig args fs) (Map.toList g) of
        Just terms -> addIneq (foldl' linPlus (linConstant (negate b)) terms) fs
        Nothing    -> fs
    term untouched sig args fs (ParamPlace k steps, n) = do
        arg <- lookup k (zip [0 ..] args)
        linScale n <$> case steps of
            [] -> do
                Just param <- lookup k (zip [0 ..] (sigParams sig))
                let iv = intValue ctx fs arg
                guard (keepsValue (ivType iv) (integerType env (paramType param)) (ivRange iv))
                l <- exactForm iv
                l <$ guard (all untouched (Map.keys (linVars l)))
            _ -> case arg of
                Fix (VarExpr (L _ _ v)) | unchangeable ctx v -> do
                    steps' <- argSteps (fixedArg args) steps
                    linVar <$> placeName ctx (Path v steps')
                _ -> Nothing
    -- What a pointer argument points to: a variable whose address it is,
    -- or what a variable the call can't change points to.
    storedIn args fs (k, r) = fromMaybe fs $ do
        arg <- lookup k (zip [0 ..] args)
        name <- case arg of
            Fix (UnaryExpr C.UopAddress (Fix (VarExpr (L _ _ v)))) -> Just v
            Fix (VarExpr (L _ _ v)) | unchangeable ctx v -> placeName ctx (Path v [Deref])
            _ -> Nothing
        return (setRange name (intersectRange r (placeRange ctx name fs)) fs)
    sized fe untouched sig args fs (ParamPlace k steps, l) = fromMaybe fs $ do
        steps' <- argSteps (fixedArg args) steps
        -- A variable the call can't change, or the address of a place (what
        -- it points to is that place).
        path <- case drop k args of
            Fix (VarExpr (L _ _ v)) : _ | unchangeable ctx v -> Just (Path v steps')
            Fix (UnaryExpr C.UopAddress x) : _
                | Just p <- canonical ctx <$> pathOf x, unchangeable ctx (pathRoot p), Deref : rest <- steps' ->
                    Just p { pathSteps = pathSteps p ++ rest }
            _ -> Nothing
        name <- placeName ctx path
        terms <- traverse (\(p, n) -> do
                    j <- T.stripPrefix "#" p >>= readMaybe . T.unpack
                    arg <- listToMaybe (drop j args)
                    Just param <- listToMaybe (drop j (sigParams sig))
                    let iv = intValue ctx fs arg
                    guard (keepsValue (ivType iv) (integerType env (paramType param)) (ivRange iv))
                    form <- exactForm iv
                    guard (all untouched (Map.keys (linVars form)))
                    return (linScale n form)) (Map.toList (linVars l))
        let size = foldl' linPlus (linConstant (linConst l)) terms
        -- What was known of it stays, unless this is known to be no less.
        case fs of
            Facts{fPointers = ps, fInts = is}
                | Just (Pointer _ (Size known)) <- Map.lookup name ps
                , Map.lookup (offsetVar name) is == Just (exactly 0)
                , not (maybe False (>= 0) (lowerLin fs (size `linMinus` known))) -> Nothing
            _ -> return (setNewPointer name (newOrigin name fe) (Size size) fs)

narrowed :: FunctionCtx Text -> Bool -> C.Node (Lexeme Text) -> Facts -> Facts
narrowed _ _ _ Unreached = Unreached
narrowed ctx truth (Fix node) facts = case node of
    ParenExpr e -> narrow ctx truth e facts
    UnaryExpr C.UopNot e -> narrow ctx (not truth) e facts
    BinaryExpr a C.BopAnd b
        | truth     -> narrow ctx True b (narrow ctx True a facts)
        | otherwise -> joinFacts (sizeHints ctx) (narrow ctx False a facts) (narrow ctx False b facts)
    BinaryExpr a C.BopOr b
        | truth     -> joinFacts (sizeHints ctx) (narrow ctx True a facts) (narrow ctx True b facts)
        | otherwise -> narrow ctx False b (narrow ctx False a facts)
    -- A buffer that's nullptr has no elements, and so a length kept with
    -- it says it has none.
    BinaryExpr a op b
        | op `elem` [C.BopEq, C.BopNe], isNullptr b -> nullAs (truth == (op == C.BopEq)) a
        | op `elem` [C.BopEq, C.BopNe], isNullptr a -> nullAs (truth == (op == C.BopEq)) b
    -- Both sides are compared in their common type: what's known of them
    -- says something only if neither changes on the way, or, for equal
    -- ones, if they can't be all the type's numbers apart.
    BinaryExpr a op b
        | Just op' <- comparison op
        , let op'' = if truth then op' else negateCmp op'
        , let ia = intValue ctx facts a
        , let ib = intValue ctx facts b
        , let t = commonType <$> ivType ia <*> ivType ib
        , all (\iv -> keepsValue (ivType iv) t (ivRange iv)) [ia, ib] || op'' == CEq && closer t [ia, ib] ->
        let -- A variable on one side gets bounds (and so do those made from
            -- it); the whole comparison is kept as a sum too.
            withBounds = case (exactForm ia >>= single, exactForm ib >>= single) of
                (Just (v, k), _) -> boundWithRelated v (shiftRange (negate k) (ivRange ib)) op'' facts
                (_, Just (v, k)) -> boundWithRelated v (shiftRange (negate k) (ivRange ia)) (flipCmp op'') facts
                _                -> facts
        in case (exactForm ia, exactForm ib) of
            (Just fa, Just fb) -> equated op'' fa fb (none op'' fa fb (foldl' (flip addIneq) withBounds (compared op'' (fa `linMinus` fb) ++ unequal op'' (fa `linMinus` fb))))
            _                  -> withBounds
    -- What a function has made sure of where it returns true holds of what
    -- it was given.
    FunctionCall (Fix (VarExpr (L _ _ f))) args
        | truth, Just checked <- Map.lookup f (envTrue (fcEnv ctx)), Just sig <- Map.lookup f (envFunctions (fcEnv ctx)) ->
            foldl' (given sig args) facts (Map.toList checked)
    _ | maybe False isPointerType (exprType ctx (Fix node)) -> nullAs (not truth) (Fix node)
    _ -> facts
  where
    -- Only a buffer still as it was given with its length (a parameter, a
    -- field): nullptr from an allocation says nothing of the size asked for.
    nullAs isNull p
        | isNull
        , Just v <- placeOf ctx p
        , Just (Pointer o (Size (Lin vars 0))) <- Map.lookup v (fPointers facts)
        , o == arrayOrigin v
        , [(len, 1)] <- Map.toList vars
        , not ("size(" `T.isPrefixOf` len)
        , Map.lookup (offsetVar v) (fInts facts) == Just (exactly 0)
        = addIneq (linScale (-1) (linVar len)) facts
        | otherwise = facts
    -- Numbers converted to a type of w bits are equal there only if they
    -- were, when they're less than 2^w apart.
    closer t ivs =
        let ranges = [ maybe id (intersectRange . itCanHold) (ivType iv) (ivRange iv) | iv <- ivs ]
        in case (traverse rLow ranges, traverse rHigh ranges) of
            (Just los, Just his) -> maximum his - minimum los < 2 ^ fewestBits t
            _                    -> False
    -- An argument that's a variable plus a constant, unchanged by the
    -- conversion to its parameter's type, is so much less than the range.
    given sig args fs (k, r)
        | Just arg <- lookup k (zip [0 ..] args)
        , Just (Just param) <- lookup k (zip [0 ..] (sigParams sig))
        , let iv = intValue ctx fs arg
        , keepsValue (ivType iv) (integerType (fcEnv ctx) (paramType param)) (ivRange iv)
        , Just (v, c) <- exactForm iv >>= single
        = boundWithRelated v (shiftRange (negate c) r) CEq fs
        | otherwise = fs
    -- A variable plus a constant.
    single (Lin vars c) = case Map.toList vars of
        [(v, 1)] -> Just (v, c)
        _        -> Nothing
    shiftRange k (Range lo hi) = Range ((+ k) <$> lo) ((+ k) <$> hi)
    -- Two variables found equal, each with a constant.
    equated cmp (Lin va ca) (Lin vb cb) fs
        | cmp == CEq, [(v, 1)] <- Map.toList va, [(w, 1)] <- Map.toList vb, v /= w = equate v w (cb - ca) fs
    equated _ _ _ fs = fs
    -- A variable found to be the number for none or not ('unlessNone').
    none cmp fa fb fs
        | cmp `elem` [CEq, CNe]
        , Just (v, k) <- case (Map.toList (linVars fa), Map.toList (linVars fb)) of
            ([(x, 1)], []) | linConst fa == 0 -> Just (x, linConst fb)
            ([], [(x, 1)]) | linConst fb == 0 -> Just (x, linConst fa)
            _                                 -> Nothing
        , let z = noneVar v k
        , Facts{fIneqs = ineqs} <- fs
        , Map.lookup (Map.fromList [(v, 1), (z, negate k)]) ineqs == Just 0 =
            settle z (if cmp == CEq then 1 else 0) fs
        | otherwise = fs
    -- A sum known to be at least 0, or at most, and not 0, is past it.
    unequal cmp f
        | cmp /= CNe = []
        | lowerLin facts f == Just 0 = [f `linMinus` linConstant 1]
        | upperLin facts f == Just 0 = [linScale (-1) f `linMinus` linConstant 1]
        | otherwise = []
    -- What f `cmp` 0 says, as sums at least 0.
    compared cmp f = case cmp of
        CGe -> [f]
        CGt -> [f `linMinus` linConstant 1]
        CLe -> [linScale (-1) f]
        CLt -> [linScale (-1) f `linMinus` linConstant 1]
        CEq -> [f, linScale (-1) f]
        CNe -> []
    -- A bound on v is one on the variable it is made from (v = root + c),
    -- and on everything else made from that (u = root + d, so u = v - c + d).
    boundWithRelated v r cmp fs =
        let linear = case fs of
                Unreached -> Map.empty
                _         -> fLinear fs
            (root, offset) = fromMaybe (v, 0) (Map.lookup v linear)
            related = [ (root, negate offset) | root /= v ]
                   ++ [ (u, d - offset) | (u, (w, d)) <- Map.toList linear, w == root, u /= v ]
        in foldl' (\acc (x, c) -> bound x (shiftRange c r) cmp acc) (bound v r cmp fs) related
    bound v (Range lo hi) cmp fs =
        let current = placeRange ctx v fs
            -- Not one value: not it at either end.
            point = if lo == hi then lo else Nothing
            newLow = case cmp of
                CGt                                           -> (+ 1) <$> lo
                CGe                                           -> lo
                CEq                                           -> lo
                CNe | Just k <- point, rLow current == Just k -> Just (k + 1)
                _                                             -> Nothing
            newHigh = case cmp of
                CLt -> subtract 1 <$> hi
                CLe -> hi
                CEq -> hi
                CNe | Just k <- point, rHigh current == Just k -> Just (k - 1)
                _   -> Nothing
        in setRange v (intersectRange current (Range newLow newHigh)) fs

------------------------------------------------------------------------------
-- Checking calls
------------------------------------------------------------------------------

-- | A call whose argument can't be shown to be big enough.
data Failure = Failure
    { flLoc         :: Maybe (Lexeme Text)
    , flKind        :: FailureKind
    , flKnown       :: Maybe Integer
    , flRequirement :: Maybe (Text, Integer)
      -- ^ The variable whose lower bound it depends on, and the least that
      -- variable would need to be.
    , flDeficit     :: Maybe (Lin, Lin)
      -- ^ The buffer's size and what it needs, as sums: what a function needs
      -- of a buffer it's given, if the size is the buffer's ('sizeName').
    }

-- | What an argument can't be shown to be.
data FailureKind
    = TooShort Text Int Integer
      -- ^ An argument (from 1) with at least so many elements
      -- ('ArgumentTooShort').
    | TooSmall Text Int Integer
      -- ^ An integer argument at least so big ('ArgumentTooSmall').
    | TooBig Text Int Integer
      -- ^ An integer argument at most so big ('ArgumentTooBig').
    | PointsTooHigh Text Int Integer
      -- ^ An argument pointing to an integer at most so big
      -- ('PointeeTooBig').
    | Unbalanced Text [(Integer, Int)] Integer
      -- ^ Integer arguments (from 1) so many times each, and a number, that
      -- make at least 0 ('ArgumentsUnbalanced').
    | ShorterThanLength Text Int Int (Maybe Integer)
      -- ^ An argument with the elements the length argument says, which
      -- can be up to so many ('ArgumentShorterThanLength').
    | ShorterThanNeeded Text Int (Maybe Integer)
      -- ^ An argument with as many elements as the function needs, which
      -- can be up to so many ('ArgumentShorterThanNeeded').
    | PairShorterThanLength Pair (Maybe Integer)
      -- ^ A buffer with the elements its length says, which can be up to
      -- so many ('BufferShorterThanLength').
    | CountOverCapacity Text Text
      -- ^ A count and the capacity it must be at most ('CountAboveCapacity').
    | AssertFails Text
      -- ^ A comparison an assert says holds ('AssertMayFail').
    | ToUnsigned Text Text Range
      -- ^ A signed number converted to an unsigned type, as written, the
      -- type, and what it can be ('NegativeToUnsigned').
    | ToSigned Text Text Range
      -- ^ An unsigned number converted to a signed type, as written, the
      -- type, and what it can be ('TooBigForSigned').
    | OutOfBounds Text Text Range
      -- ^ An index into an array or through a pointer, as written, and what
      -- it can be ('IndexOutOfBounds').
    | MovedPast Text Text Range
      -- ^ A pointer moved forward, and by what, as written, and what that
      -- can be ('PointerPastEnd').
    | Overflows (Maybe Integer) (Maybe Integer) Integer Integer
      -- ^ Signed arithmetic the numbers of which can be more than its type
      -- holds ('SignedOverflow').

failureError :: FilePath -> Failure -> ErrorInfo p
failureError file fl =
    ErrorInfo (flLoc fl) [InFile file] err []
  where
    err = case flKind fl of
        TooShort f i needed            -> ArgumentTooShort f i needed (flKnown fl)
        TooSmall f i needed            -> ArgumentTooSmall f i needed (flKnown fl)
        TooBig f i most                -> ArgumentTooBig f i most (flKnown fl)
        PointsTooHigh f i most         -> PointeeTooBig f i most (flKnown fl)
        Unbalanced f terms c           -> ArgumentsUnbalanced f terms c (flKnown fl)
        ShorterThanLength f i j most   -> ArgumentShorterThanLength f i j (flKnown fl) most
        ShorterThanNeeded f i most     -> ArgumentShorterThanNeeded f i (flKnown fl) most
        PairShorterThanLength pr most  -> BufferShorterThanLength (prBuffer pr) (prLength pr) (flKnown fl) most
        CountOverCapacity c capacity   -> CountAboveCapacity c capacity
        Overflows lo hi least most     -> SignedOverflow lo hi least most
        AssertFails cond               -> AssertMayFail cond
        OutOfBounds arr ix r           -> IndexOutOfBounds arr ix (flKnown fl) (rLow r) (rHigh r)
        MovedPast ptr by r             -> PointerPastEnd ptr by (flKnown fl) (rLow r) (rHigh r)
        ToUnsigned what ty r           -> NegativeToUnsigned what ty (rLow r)
        ToSigned what ty r             -> TooBigForSigned what ty (rHigh r)

-- | The calls in a statement whose arguments can't be shown to be big enough.
checkStmt :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> [Failure]
checkStmt _ Unreached _ = []
checkStmt _ _ (Fix (ExprStmt (Fix (FunctionCall (Fix (VarExpr (L _ _ assume))) _))))
    -- The condition is checked where it's evaluated, not in each branch.
    | "__tokstyle_assume_" `T.isPrefixOf` assume = []
checkStmt ctx facts stmt =
    assertFailures ctx facts stmt
    ++ concat [ callFailures ctx fs call | (fs, call) <- callsWithFacts ctx facts stmt ]
    ++ concat [ indexFailures ctx fs a i addr | (fs, addr, Fix (ArrayAccess a i)) <- evaluated ]
    -- A pointer moved forward is where an element is, as with @&a[i]@:
    -- in its buffer, or just past its end.
    ++ concat [ map moved (indexFailures ctx fs p i True)
              | (fs, _, Fix (BinaryExpr a C.BopPlus b)) <- evaluated
              , (p, i) <- [ (a, b) | pointerSide ctx fs a ] ++ [ (b, a) | not (pointerSide ctx fs a), pointerSide ctx fs b ] ]
    ++ concat [ conversionFailures ctx fs (typeOfDecl ty) (showNodePlain ty) e | (fs, _, Fix (CastExpr ty e)) <- evaluated ]
    -- Conversions without a cast: what's assigned, given for a parameter,
    -- returned, or a variable starts as.
    ++ concat [ conversionFailures ctx fs t (ctName t) rhs | (fs, _, Fix (AssignExpr lhs C.AopEq rhs)) <- evaluated, Just t <- [exprType ctx lhs] ]
    ++ concat [ conversionFailures ctx fs (paramType param) (ctName (paramType param)) arg
              | (fs, _, Fix (FunctionCall f args)) <- evaluated
              , Just (_, sig) <- [signatureOf ctx f]
              , (Just param, arg) <- zip (sigParams sig) args ]
    ++ case unFix stmt of
        Return (Just e) | Just (L _ _ name) <- fcLoc ctx, Just sig <- Map.lookup name (envFunctions (fcEnv ctx)) ->
            conversionFailures ctx facts (sigReturn sig) (ctName (sigReturn sig)) e
        VarDeclStmt (Fix (VarDecl ty _ [])) (Just e) -> conversionFailures ctx facts (typeOfDecl ty) (ctName (typeOfDecl ty)) e
        _ -> []
    -- Pairs something else can see: what calls are given, what a variable
    -- pointed to before it's given something else, and everything that
    -- outlives the function where it returns.
    ++ concat [ checkPairs ctx facts (getLexeme f) prs | (f, prs) <- called ]
    ++ concat [ checkPairs ctx facts (Just l) (unseen (filter prOutlives (pairsTouching ctx (pathsWith ctx v))))
              | l@(L _ _ v) <- concatMap assigned exprs ]
    ++ case unFix stmt of
        Return mExpr -> checkPairs ctx facts ((mExpr >>= getLexeme) <|> fcLoc ctx) (unseen (filter prOutlives (fcPairs ctx)))
        _            -> []
  where
    evaluated = evaluatedWithFacts ctx facts stmt
    exprs = statementExprs stmt
    moved fl = case flKind fl of
        OutOfBounds p i r -> fl { flKind = MovedPast p i r }
        _                 -> fl
    called = [ (f, pairsTouching ctx (callReach ctx call)) | call@(f, _) <- callsIn exprs ]
    unseen = filter (`notElem` concatMap snd called)
    assigned (Fix n) = case n of
        AssignExpr (Fix (VarExpr l)) _ _      -> [l]
        UnaryExpr C.UopIncr (Fix (VarExpr l)) -> [l]
        UnaryExpr C.UopDecr (Fix (VarExpr l)) -> [l]
        _                                     -> []

-- | The calls in a statement's expressions, with what's known where each
-- is made: past the left of @&&@ and @||@, and in the side of @?:@ it's in.
callsWithFacts :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> [(Facts, Call)]
callsWithFacts ctx = go
  where
    go Unreached _ = []
    go facts (Fix node) = case node of
        IfStmt c _ _              -> go facts c
        WhileStmt c _             -> go facts c
        DoWhileStmt _ c           -> go facts c
        ForStmt i _ _ _           -> go facts i
        SwitchStmt c _            -> go facts c
        CompoundStmt _            -> []
        TernaryExpr c a b         -> go facts c ++ go (narrow ctx True c facts) a ++ go (narrow ctx False c facts) b
        BinaryExpr a C.BopAnd b   -> go facts a ++ go (narrow ctx True a facts) b
        BinaryExpr a C.BopOr b    -> go facts a ++ go (narrow ctx False a facts) b
        FunctionCall f args       -> (facts, (f, args)) : concatMap (go facts) (f : args)
        _                         -> concatMap (go facts) (toList node)

-- | The expressions a statement evaluates, with what's known where each
-- is, and whether it's only where something is (under @&@, so an element
-- may be one past the last). Not what @sizeof@ is of, which isn't
-- evaluated.
evaluatedWithFacts :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> [(Facts, Bool, C.Node (Lexeme Text))]
evaluatedWithFacts ctx = go False
  where
    go _ Unreached _ = []
    go addr facts e@(Fix node) = case node of
        IfStmt c _ _              -> go False facts c
        WhileStmt c _             -> go False facts c
        DoWhileStmt _ c           -> go False facts c
        ForStmt i _ _ _           -> go False facts i
        SwitchStmt c _            -> go False facts c
        CompoundStmt _            -> []
        SizeofExpr _              -> []
        TernaryExpr c a b         -> here ++ go False facts c ++ go addr (narrow ctx True c facts) a ++ go addr (narrow ctx False c facts) b
        BinaryExpr a C.BopAnd b   -> here ++ go False facts a ++ go False (narrow ctx True a facts) b
        BinaryExpr a C.BopOr b    -> here ++ go False facts a ++ go False (narrow ctx False a facts) b
        UnaryExpr C.UopAddress x  -> here ++ go True facts x
        ParenExpr x               -> here ++ go addr facts x
        _                         -> here ++ concatMap (go False facts) (toList node)
      where
        here = [(facts, addr, e)]

-- | An index that can't be shown to be in bounds: at least 0, and less than
-- how many elements there are (or as many, for where one is).
indexFailures :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> C.Node (Lexeme Text) -> Bool -> [Failure]
indexFailures ctx facts a i addr =
    [ Failure (getLexeme a) (OutOfBounds (showNodePlain a) (showNodePlain i) r) (max 0 <$> (size >>= lowerBound facts)) Nothing deficit
    | not (nonNegative && fits) ]
  where
    r = rangeOf ctx facts i
    size = sizeOf ctx facts a
    nonNegative = maybe False (>= 0) (rLow r)
    past = if addr then 0 else 1 :: Integer
    needed = linPlus (linConstant past) <$> formOf ctx facts i
    fits = holdsLength facts size needed (rangeArith C.BopPlus r (exactly past))
    -- A pointer parameter of unknown size, indexed below the integer
    -- parameter after it: it needs as many elements as that says.
    deficit = listToMaybe
        [ (l', normalise facts (linVar n `linPlus` rest))
        | nonNegative
        , Just (Size l) <- [size]
        , Just need <- [needed]
        , let l' = normalise facts l
        , (p, n) <- zip (fcArgs ctx) (drop 1 (fcArgs ctx))
        , let sz = sizeName p
        , Map.lookup sz (linVars l') == Just 1
        , let rest = l' `linMinus` linVar sz
        , maybe False (isJust . integerType (fcEnv ctx)) (Map.lookup n (fcTypes ctx))
        , maybe False (>= 0) (lowerLin facts (linVar n `linPlus` rest `linMinus` need))
        ]

-- | A signed number converted to an unsigned type (as written) where it
-- can't be shown not to be negative, which the conversion would change.
conversionFailures :: FunctionCtx Text -> Facts -> CType -> Text -> C.Node (Lexeme Text) -> [Failure]
conversionFailures ctx facts ty written e =
    [ Failure (getLexeme e) (ToUnsigned (showNodePlain e) written r) Nothing Nothing Nothing
    | Just to <- [integerType env ty]
    , not (itSigned to)
    , Just from <- [ivType iv]
    , itSigned from
    , not (maybe False (>= 0) (rLow r))
    ] ++
    -- An unsigned number made signed must fit, or it comes out negative;
    -- unless it's a sum that comes out right there (done unsigned from
    -- signed numbers, and back).
    [ Failure (getLexeme e) (ToSigned (showNodePlain e) written r) Nothing Nothing Nothing
    | Just to <- [integerType env ty]
    , itSigned to
    , Just from <- [ivType iv]
    , not (itSigned from)
    , Just most <- [rHigh (itCanHold to)]
    , not (maybe False (<= most) (rHigh r))
    , isNothing (exactForm (convertValue ctx facts (Just to) iv))
    ]
  where
    env = fcEnv ctx
    iv = intValue ctx facts e
    -- Also what's known of how it relates to others.
    r = maybe (ivRange iv) (\l -> intersectRange (ivRange iv) (rangeOfLin (typedFacts ctx facts l) l)) (exactForm iv)

-- | What a call needs of its arguments that can't be shown where it's made.
callFailures :: FunctionCtx Text -> Facts -> Call -> [Failure]
callFailures ctx facts = check
  where
    env = fcEnv ctx
    check (f, args) = case signatureOf ctx f of
        Nothing -> []
        Just (name, sig) ->
            let requires = Map.findWithDefault Map.empty name (envRequires env)
            in [ Failure (getLexeme f) (TooShort name i needed) known (requirement size needed) (deficit size (linConstant needed))
               | (i, Just param, arg) <- zip3 [1 ..] (sigParams sig ++ repeat Nothing) args
               -- What a parameter needs is its most: a lower bound would ask
               -- too little.
               , Just needed <- [case ctDims (paramType param) of
                                     (Range _ (Just n) : _) -> Just n
                                     _                      -> Nothing]
               -- Whether nullptr may be passed is the nullability check's.
               , let size = argumentSize ctx facts param arg
               , size /= Just NullPointer
               , let known = max 0 <$> (size >>= lowerBound facts)
               , maybe True (< needed) known
               ]
            -- What the function needs of its integer parameters: as a sum
            -- the argument is, or one it's at most, put against the bound.
            ++ [ Failure (getLexeme f) (TooSmall name (k + 1) needed) known (form >>= single needed) ((\l -> (normalise facts l, linConstant needed)) <$> form)
               | (k, arg, param) <- zip3 [0 ..] args (sigParams sig ++ repeat Nothing)
               , Just needed <- [Map.lookup k requires >>= rLow]
               , let paramInt = param >>= integerType env . paramType
               , let known = rLow (convertedRange ctx facts paramInt arg)
               , let form = convertedForm ctx facts paramInt arg
               , maybe True (< needed) known
               , not (maybe False (\l -> maybe False (>= 0) (lowerLin facts (l `linMinus` linConstant needed))) form)
               ]
            ++ [ Failure (getLexeme f) (TooBig name (k + 1) most) known Nothing ((\l -> (linConstant most, normalise facts l)) <$> listToMaybe uppers)
               | (k, arg, param) <- zip3 [0 ..] args (sigParams sig ++ repeat Nothing)
               , Just most <- [Map.lookup k requires >>= rHigh]
               , let paramInt = param >>= integerType env . paramType
               , let known = rHigh (convertedRange ctx facts paramInt arg)
               , let uppers = convertedUpper ctx facts paramInt arg
               , maybe True (> most) known
               , not (any (\l -> maybe False (>= 0) (lowerLin facts (linConstant most `linMinus` l))) uppers)
               ]
            -- What the function needs of what it's given pointers to.
            ++ [ Failure (getLexeme f) (PointsTooHigh name (k + 1) most) known Nothing Nothing
               | (k, most) <- Map.toList (Map.findWithDefault Map.empty name (envPointsAtMost env))
               , Just arg <- [lookup k (zip [0 ..] args)]
               , let iv = intValue ctx facts (pointee arg)
                     known = rHigh (ivRange iv)
               , maybe True (> most) known
               , not (any (\l -> maybe False (>= 0) (lowerLin facts (linConstant most `linMinus` l))) (upperForms facts iv))
               ]
            -- What the function needs of how its integer arguments relate.
            ++ [ Failure (getLexeme f) (Unbalanced name terms c) (made >>= lowerLin facts) Nothing Nothing
               | Lin vars c <- Map.findWithDefault [] name (envRelations env)
               , let made = leastOf sig args (Lin vars c)
               , not (maybe False (>= 0) (made >>= lowerLin facts))
               , let terms = [ (n, k + 1) | (v, n) <- Map.toList vars, Just k <- [T.stripPrefix "#" v >>= readMaybe . T.unpack] ]
               ]
            ++ [ Failure (getLexeme f) (ShorterThanLength name (i + 1) (j + 1) most) known Nothing short
               | (i, Just param, arg) <- zip3 [0 ..] (sigParams sig ++ repeat Nothing) args
               , Just j <- [paramLength param]
               , Just lenArg <- [lookup j (zip [0 ..] args)]
               , let lenInt = case drop j (sigParams sig) of
                         Just lenParam : _ -> integerType env (paramType lenParam)
                         _                 -> Nothing
               , Just (known, most, short) <- [shorterThan facts param lenInt arg lenArg]
               ]
            -- What the function needs of the buffers it's given, with the
            -- arguments put in.
            -- A need is passed on only if something other than the types
            -- bounds it.
            ++ [ Failure (getLexeme f) (ShorterThanNeeded name (k + 1) most) (max 0 <$> (size >>= lowerBound facts)) Nothing
                     (deficit size =<< instantiate (boundedMost ctx facts) sig args need)
               | (k, needs) <- Map.toList (Map.findWithDefault Map.empty name (envNeeds env))
               , Just (Just param) <- [lookup k (zip [0 ..] (sigParams sig))]
               , Just arg <- [lookup k (zip [0 ..] args)]
               , let size = argumentSize ctx facts param arg
               , size /= Just NullPointer
               , let unmet = [ (need, needed) | need <- needs, let needed = instantiate (\t -> rHigh . convertedRange ctx facts t) sig args need
                                              , not (maybe False (\n -> holdsLength facts size (Just n) (rangeOfLin facts n)) needed) ]
               , (need, _) : _ <- [unmet]
               , let most = maximum (map ((>>= \l -> upperLin (typedFacts ctx facts l) l) . snd) unmet)
               ]
    pointee arg = case unFix arg of
        ParenExpr x              -> pointee x
        UnaryExpr C.UopAddress x -> x
        _                        -> Fix (UnaryExpr C.UopDeref arg)
    -- A sum of integer arguments put in: their values, or what makes it
    -- least if those aren't sums.
    leastOf sig args (Lin vars c) = foldl' plus (Just (linConstant c)) (Map.toList vars)
      where
        plus acc (v, n) = do
            sumSoFar <- acc
            k <- T.stripPrefix "#" v >>= readMaybe . T.unpack
            arg <- lookup k (zip [0 :: Int ..] args)
            let t = case drop k (sigParams sig) of
                    Just param : _ -> integerType env (paramType param)
                    _              -> Nothing
                r = convertedRange ctx facts t arg
            term <- case convertedForm ctx facts t arg of
                Just l  -> Just (linScale n l)
                Nothing -> linConstant . (* n) <$> (if n > 0 then rLow r else rHigh r)
            return (sumSoFar `linPlus` term)
    -- A need with the arguments put in: their values, or the most they can
    -- be if those aren't sums.
    instantiate mostOf sig args (Lin vars c) = foldl' plus (Just (linConstant c)) (Map.toList vars)
      where
        plus acc (v, n) = do
            sumSoFar <- acc
            k <- T.stripPrefix "#" v >>= readMaybe . T.unpack
            arg <- lookup k (zip [0 :: Int ..] args)
            let t = case drop k (sigParams sig) of
                    Just param : _ -> integerType env (paramType param)
                    _              -> Nothing
            term <- case convertedForm ctx facts t arg of
                Just l  -> Just (linScale n l)
                Nothing -> linConstant . (* n) <$> (if n > 0 then mostOf t arg else rLow (convertedRange ctx facts t arg))
            return (sumSoFar `linPlus` term)
    deficit size needed = case size of
        Just (Size l) -> Just (normalise facts l, normalise facts needed)
        _             -> Nothing
    -- How much a buffer is known to have and the most its length can be,
    -- if it can't be shown to have that many: on each side of a choice of
    -- length under its condition, and in elements of what it holds for a
    -- count of them times their size.
    shorterThan fs param lenInt arg lenArg = case unFix lenArg of
        _ | Unreached <- fs -> Nothing
        ParenExpr x -> shorterThan fs param lenInt arg x
        TernaryExpr c a b -> case catMaybes [ shorterThan (narrow ctx True c fs) param lenInt arg a
                                            , shorterThan (narrow ctx False c fs) param lenInt arg b ] of
            []    -> Nothing
            sides -> Just (minimum [ k | (k, _, _) <- sides ], maximum [ m | (_, m, _) <- sides ], Nothing)
        _ | Just count <- elementCount param arg lenArg ->
            measured fs (sizeOf ctx fs arg <|> Just (elements 1)) (upperForms fs (intValue ctx fs count)) (rangeOf ctx fs count) (boundedMost ctx fs Nothing count)
          | otherwise ->
            measured fs (argumentSize ctx fs param arg) (convertedUpper ctx fs lenInt lenArg) (convertedRange ctx fs lenInt lenArg) (boundedMost ctx fs lenInt lenArg)
    measured fs size lenForms lenRange lenMost
        | size == Just NullPointer || any (\l -> holdsLength fs size l lenRange) (Nothing : map Just lenForms) = Nothing
        | otherwise = Just (max 0 <$> (size >>= lowerBound fs), rHigh lenRange, short)
      where
        short = case size of
            Just (Size l) -> (,) (normalise fs l) . normalise fs <$> (listToMaybe lenForms <|> linConstant <$> lenMost)
            _             -> Nothing
    -- A length in bytes that is a count times the size of what the buffer
    -- holds: the count.
    elementCount param arg lenArg = do
        t <- resolveType env <$> exprType ctx arg
        let element = elementOf t
        guard (isPointerType t && isByteType env (elementOf (resolveType env (paramType param))) && not (isByteType env element))
        case unFix lenArg of
            BinaryExpr a C.BopMul b
                | sizeOfType a == Just element -> Just b
                | sizeOfType b == Just element -> Just a
            _ -> Nothing
    sizeOfType (Fix n) = case n of
        ParenExpr x  -> sizeOfType x
        SizeofType t -> Just (resolveType env (typeOfDecl t))
        SizeofExpr x -> resolveType env <$> exprType ctx x
        _            -> Nothing
    -- A size measured from a variable needs that variable to be at least
    -- what's needed plus what was taken off it.
    requirement (Just (Size l)) needed = single needed l
    requirement _ _                    = Nothing
    -- A sum that is 1 variable (the one everything is made from) plus a
    -- constant needs that variable to be at least what's needed less the
    -- constant.
    single needed l = case normalise facts l of
        Lin vars c | [(v, 1)] <- Map.toList vars -> Just (v, needed - c)
        _                                        -> Nothing

-- | The comparisons of integers an assert says hold that can't be shown to
-- here (that they don't would leave nothing to go on with, or what they
-- need is at least 0). Each is reported,
-- with what's short of it as for a call: what a function asserts of its
-- parameters, its callers are held to.
assertFailures :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> [Failure]
assertFailures ctx facts@Facts{} (Fix (ExprStmt (Fix (FunctionCall (Fix (VarExpr (L _ _ "assert"))) [cond])))) =
    [ Failure (getLexeme c) (AssertFails (showNodePlain c)) Nothing Nothing (short c)
    | c <- conjuncts cond
    , comparesIntegers c
    , narrow ctx False c facts /= Unreached
    , not (maybe False (\ls -> not (null ls) && all atLeast0 ls) (holding c))
    ]
  where
    conjuncts (Fix n) = case n of
        ParenExpr e             -> conjuncts e
        BinaryExpr a C.BopAnd b -> conjuncts a ++ conjuncts b
        _                       -> [Fix n]
    comparesIntegers (Fix n) = case n of
        BinaryExpr a op b -> isJust (comparison op) && integer a && integer b
        _                 -> False
    integer e = not (pointerSide ctx facts e) && isJust (ivType (intValue ctx facts e))
    -- The sums at least 0 if a comparison holds, in the type it's done in:
    -- b - (a + 1) for a < b.
    holding (Fix (BinaryExpr a op b)) = do
        t <- commonType <$> (promote <$> ivType (intValue ctx facts a)) <*> (promote <$> ivType (intValue ctx facts b))
        la <- convertedForm ctx facts (Just t) a
        lb <- convertedForm ctx facts (Just t) b
        return $ case op of
            C.BopLt -> [lb `linMinus` la `linMinus` linConstant 1]
            C.BopLe -> [lb `linMinus` la]
            C.BopGt -> [la `linMinus` lb `linMinus` linConstant 1]
            C.BopGe -> [la `linMinus` lb]
            C.BopEq -> [lb `linMinus` la, la `linMinus` lb]
            _       -> []
    holding _ = Nothing
    atLeast0 l = maybe False (>= 0) (lowerLin (typedFacts ctx facts l) l)
    -- What's short of it, as for a call: only one sum.
    short c = case holding c of
        Just [l] -> Just (normalise facts l, linConstant 0)
        _        -> Nothing
assertFailures _ _ _ = []

-- | Signed arithmetic in a statement whose numbers can be more than its
-- type holds: undefined, so it's reported here and assumed not to happen
-- everywhere else. Each side of a choice, @&&@ or @||@ is seen under what's
-- known where it's evaluated. A result that's a sum is also bounded by how
-- its variables relate, each within what its type holds.
overflowFailures :: FunctionCtx Text -> Facts -> C.Node (Lexeme Text) -> [Failure]
overflowFailures ctx = go
  where
    env = fcEnv ctx
    go Unreached _ = []
    go facts e@(Fix node) = case node of
        IfStmt c _ _ -> go facts c
        WhileStmt c _ -> go facts c
        DoWhileStmt _ c -> go facts c
        ForStmt i _ _ _ -> go facts i
        SwitchStmt c _ -> go facts c
        CompoundStmt _ -> []
        TernaryExpr c a b -> go facts c ++ go (narrow ctx True c facts) a ++ go (narrow ctx False c facts) b
        BinaryExpr a C.BopAnd b -> go facts a ++ go (narrow ctx True a facts) b
        BinaryExpr a C.BopOr b -> go facts a ++ go (narrow ctx False a facts) b
        BinaryExpr a op b
            | op `elem` [C.BopPlus, C.BopMinus, C.BopMul]
            , not (pointerSide ctx facts a || pointerSide ctx facts b) ->
                let ia = intValue ctx facts a
                    ib = intValue ctx facts b
                    t = binaryType op (ivType ia) (ivType ib)
                in past facts e t (rangeArith op (converted facts t ia) (converted facts t ib)) (exactForm (intValue ctx facts e))
                    ++ go facts a ++ go facts b
        UnaryExpr C.UopMinus x ->
            let ix = intValue ctx facts x
                t = promote <$> ivType ix
            in past facts e t (rangeArith C.BopMinus (exactly 0) (converted facts t ix)) (exactForm (intValue ctx facts e)) ++ go facts x
        AssignExpr lhs op rhs
            | Just bop <- lookup op [(C.AopPlus, C.BopPlus), (C.AopMinus, C.BopMinus), (C.AopMul, C.BopMul)]
            , Just t <- exprType ctx lhs >>= integerType env
            , let ir = intValue ctx facts rhs
            , undefinedIn t (ivType ir) ->
                let sumForm = guard (bop /= C.BopMul) >> (if bop == C.BopPlus then linPlus else linMinus) <$> formOf ctx facts lhs <*> exactForm ir
                in past facts e (Just t) (rangeArith bop (rangeOf ctx facts lhs) (converted facts (Just t) ir)) sumForm
                    ++ go facts lhs ++ go facts rhs
        UnaryExpr op x
            | Just k <- lookup op [(C.UopIncr, 1), (C.UopDecr, -1)]
            , Just t <- exprType ctx x >>= integerType env
            , undefinedIn t (Just intType) ->
                past facts e (Just t) (rangeArith C.BopPlus (rangeOf ctx facts x) (exactly k)) ((`linPlus` linConstant k) <$> formOf ctx facts x)
                    ++ go facts x
        _ -> concatMap (go facts) (toList node)
    converted facts t = ivRange . convertValue ctx facts t
    past facts e t numbers form =
        [ Failure (getLexeme e) (Overflows (rLow r) (rHigh r) least most) Nothing Nothing Nothing
        | Just it <- [t]
        , itSigned it
        , Range (Just least) (Just most) <- [itHolds it]
        , not (numbers `within` itHolds it)
        , let r = maybe numbers (\l -> intersectRange numbers (rangeOfLin (typedFacts ctx facts l) l)) form
        , not (r `within` itHolds it)
        ]

-- | Facts with every variable a sum and the known sums are in bounded by
-- what its type holds, for working out bounds from how variables relate.
typedFacts :: FunctionCtx Text -> Facts -> Lin -> Facts
typedFacts _ Unreached _ = Unreached
typedFacts ctx facts l =
    foldl' bound facts (Set.toList (Map.keysSet (linVars l) <> foldMap Map.keysSet (Map.keys (fIneqs facts)) <> Map.keysSet (fLinear facts)))
  where
    bound fs v = case typeOfPlace ctx v >>= integerType (fcEnv ctx) of
        Just it -> setRange v (intersectRange (itCanHold it) (Map.findWithDefault unknownRange v (fInts fs))) fs
        Nothing -> fs

-- | A buffer has the elements a length says if its size less the length is
-- known to be at least 0, or its least size is at least the most the
-- length can be.
holdsLength :: Facts -> Maybe Size -> Maybe Lin -> Range -> Bool
holdsLength facts size lenForm lenRange = case size of
    Just (Size s) ->
        maybe False (>= 0) (lenForm >>= lowerLin facts . linMinus s)
        || maybe False (\most -> maybe False (>= most) (lowerLin facts s)) (rHigh lenRange)
    _ -> False

-- | Pairs whose buffer can't be shown to have the elements their length
-- says, or whose count may be more than that. Here nullptr has none.
checkPairs :: FunctionCtx Text -> Facts -> Maybe (Lexeme Text) -> [Pair] -> [Failure]
checkPairs _ Unreached _ _ = []
checkPairs ctx facts loc prs =
    [ Failure loc (CountOverCapacity (sourceNamed ctx c) (sourceNamed ctx (prLength pr))) Nothing Nothing Nothing
    | pr <- prs
    , Just c <- [prCount pr]
    , let room = linVar (prLength pr) `linMinus` linVar c
    , not (maybe False (>= 0) (lowerLin (typedFacts ctx facts room) room))
    ] ++
    [ Failure loc (PairShorterThanLength pr { prBuffer = sourceNamed ctx (prBuffer pr), prLength = sourceNamed ctx (prLength pr) } (rHigh lenRange)) (max 0 <$> (size >>= lowerBound facts)) Nothing Nothing
    | pr <- prs
    , let lenRange = maybe unknownRange (\t -> pathRange t (prLength pr) facts) (prLengthType pr)
          size = case prElements pr of
              Just n  -> Just (elements n)
              Nothing -> case Map.lookup (prBuffer pr) (fPointers facts) of
                  Just (Pointer _ (Size base)) -> Just (Size (base `linMinus` linVar (offsetVar (prBuffer pr))))
                  Just (Pointer _ NullPointer) -> Just (elements 0)
                  Nothing                      -> Nothing
    , not (holdsLength facts size (Just (linVar (prLength pr))) lenRange)
    ]

signatureOf :: FunctionCtx Text -> C.Node (Lexeme Text) -> Maybe (Text, Signature)
signatureOf ctx f = case unFix f of
    VarExpr (L _ _ name) | Just sig <- Map.lookup name (envFunctions env) -> Just (name, sig)
    _ -> do
        t <- exprType ctx f
        let t' = resolveType env t
        sig <- Map.lookup (ctName t') (envFunctions env)
        return (ctName t', sig)
  where
    env = fcEnv ctx

------------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------------

data Function = Function
    { fnFile   :: FilePath
    , fnName   :: Text
    , fnDefn   :: C.Node (Lexeme Text)
    , fnCtx    :: FunctionCtx Text
    , fnStart  :: Facts
      -- ^ What's known where it starts, from its parameters.
    , fnInit   :: Facts
      -- ^ That and what callers are checked to give it.
    , fnArgs   :: [Text]
      -- ^ Its parameters, in order.
    , fnDirect :: Bool
      -- ^ Called by its name, and never used as a value: every call to it
      -- is one the program makes by its name.
    , fnClosed :: Bool
      -- ^ Static and never used as a value: every caller is in the program.
    , fnParams :: Map Text Int
      -- ^ The parameters it never changes, by position.
    , fnStores :: Map Text Int
      -- ^ Pointers to integers among its parameters it only stores to,
      -- reads through and compares with nullptr, by position.
    , fnCopies :: Map Text Int
      -- ^ Locals it starts as what one of those points to, by the
      -- pointer's position.
    }

functionsOf :: Env -> Summaries -> Set.Set Text -> Set.Set Text -> FilePath -> C.Node (Lexeme Text) -> [Function]
functionsOf env summaries asValues called file n@(Fix node) = case node of
    FunctionDefn scope proto body -> case unFix proto of
        FunctionPrototype _ nameLexeme@(L _ _ name) params ->
            let own = [ x | Just x <- map (declType env) params ]
                -- The prototype says what each parameter is; the definition
                -- names them.
                declared = maybe [] sigParams (Map.lookup name (envFunctions env))
                params' = [ (pname, maybe ty paramType d, d >>= paramLength >>= nameAt)
                          | ((pname, ty), d) <- zip own (declared ++ repeat Nothing) ]
                nameAt i = fst <$> lookup i (zip [0 ..] own)
                locals = Map.fromList (localsOf env (Map.fromList own <> envGlobals env) body)
                types = Map.unions [locals, Map.fromList [ (p, ty) | (p, ty, _) <- params' ], envGlobals env]
                own' = Set.fromList (Map.keys locals ++ [ p | (p, _, _) <- params' ])
                isPointer v = maybe False ((\t -> ctPointers t > 0 && null (ctDims t)) . resolveType env) (Map.lookup v types)
                -- A parameter written as an array is a pointer.
                isArray v = maybe False (not . null . ctDims . resolveType env) (Map.lookup v locals)
                escaped = addressesKept isPointer isArray (envKeeps env) body <> (envMutable env `Set.difference` own')
                outs = [ (pname, out) | ((pname, _), Just d) <- zip own declared, Just out <- [paramOutLength d >>= nameAt] ]
                ctx0 = FunctionCtx env types (Set.fromList [ p | (p, _, _) <- params' ]) [ p | (p, _, _) <- params' ] escaped Map.empty [] (Just nameLexeme) (pathIndex escaped Map.empty []) summaries
                    (aliasesIn env escaped (Set.fromList (map fst own)) body) (comparedWithConstants body)
                (paths, pairs) = placesOf ctx0 own' outs body
                ctx = ctx0 { fcPaths = paths, fcPairs = pairs, fcIndex = pathIndex escaped paths pairs }
                -- Every pair holds where the function starts. A local's
                -- holds from where it's declared.
                start = trust (const True) pairs (foldl' (\fs (p, ty, mLen) -> paramFacts p ty mLen fs) noFacts params')
                    & \fs -> foldl' (\acc (sym, r) -> setRange sym r acc) fs (sizeSymbols ctx body)
                changed = assignedVars body
                unchanged = Map.fromList [ (p, k) | (k, (p, _, _)) <- zip [0 ..] params', not (Set.member p changed) ]
                closed = scope == C.Static && not (Set.member name asValues)
                direct = Set.member name called && not (Set.member name asValues)
                stores = Map.fromList
                    [ (p, k)
                    | (p, k) <- Map.toList unchanged
                    , Just ty <- [Map.lookup p types]
                    , let t = resolveType env ty
                    , ctPointers t == 1 && null (ctDims t)
                    , isJust (integerType env t { ctPointers = 0 })
                    , onlyStoredTo p body
                    ]
                copies = Map.fromList
                    [ (v, k)
                    | Fix (VarDeclStmt (Fix (VarDecl _ (L _ _ v) [])) (Just (Fix (UnaryExpr C.UopDeref (Fix (VarExpr (L _ _ p))))))) <- subnodes body
                    , Just k <- [Map.lookup p stores]
                    ]
            in [withSummaries env (Function file name n ctx start start [ p | (p, _, _) <- params' ] direct closed unchanged stores copies)]
        _ -> []
    _ -> concatMap (functionsOf env summaries asValues called file) (toList node)
  where
    -- A buffer parameter is the start of its buffer: of the size in its
    -- type, or as long as its length parameter.
    paramFacts p ty mLen fs = case (arrayElements ty, mLen) of
        (Just sz, _)      -> setPointer p (arrayOrigin p) (linConstant 0) sz fs
        (Nothing, Just len) -> setPointer p (arrayOrigin p) (linConstant 0) (Size (linVar len)) fs
        -- Any other buffer has a size that's its own, of at least what it
        -- points to.
        _ | ctPointers ty > 0 && null (ctDims ty) ->
            setPointer p (arrayOrigin p) (linConstant 0) (Size (linVar (sizeName p))) (setRange (sizeName p) (Range (Just 1) Nothing) fs)
        _ | Just t <- integerType env ty -> setRange p (itCanHold t) fs
        _ -> fs

-- | The paths a function names, and the pairs among them: a buffer field
-- and its length field (both, if it names one), and what out-parameters
-- for a buffer and its length point to.
placesOf :: FunctionCtx Text -> Set.Set Text -> [(Text, Text)] -> C.Node (Lexeme Text) -> (Map Text PathInfo, [Pair])
placesOf ctx own outs body = (Map.fromList infos, nub (fieldPairs ++ outPairs))
  where
    env = fcEnv ctx
    named = [ (e, canonical ctx p) | e <- subnodes body ++ givenPairs ++ zeroedFields, Just p <- [pathOf e], isPlace p ]
    -- The numbers of a struct given a constant of zeros, which are 0 then.
    zeroedFields =
        [ Fix (MemberAccess lhs (L (C.AlexPn 0 0 0) C.IdVar f))
        | Fix (AssignExpr lhs C.AopEq (Fix (VarExpr (L _ _ c)))) <- subnodes body
        , Set.member c (envZeroConsts env)
        , Just t <- [resolveType env <$> exprType ctx lhs]
        , ctPointers t == 0 && null (ctDims t)
        , (f, ft) <- maybe [] Map.toList (Map.lookup (ctName t) (envStructs env))
        , isJust (integerType env (resolveType env ft))
        ]
    -- What a variable pointing to a struct with pairs is given to a call
    -- for: the lengths, which what's known of the call may be about.
    givenPairs =
        [ Fix (PointerAccess a (L (C.AlexPn 0 0 0) C.IdVar l))
        | Fix (FunctionCall _ args) <- subnodes body
        , a@(Fix (VarExpr _)) <- args
        , Just t <- [resolveType env <$> exprType ctx a]
        , ctPointers t == 1 && null (ctDims t)
        , fp <- Map.findWithDefault [] (ctName t) (envPairs env)
        , l <- fpLength fp : toList (fpCount fp)
        ]
    isPlace p = case reverse (pathSteps p) of
        []               -> False
        Index _ True : _ -> False
        _                -> True
    info p ty out = (pathName p, PathInfo p (footprint env (fcTypes ctx) (reachedVar ctx) p) (resolveType env <$> ty) out)
    fieldPaths =
        [ (info buf (Just bufType) out, info len (Just lenType) out, count, bufType, lenType)
        | (e, p) <- named
        , Just (s, f) <- [fieldKey ctx e]
        , FieldPair x l c <- Map.findWithDefault [] s (envPairs env)
        , f == x || f == l || Just f == c
        , let out = outlives e
              swap g = p { pathSteps = init (pathSteps p) ++ [Field g] }
              (buf, len) = (swap x, swap l)
              fields = Map.findWithDefault Map.empty s (envStructs env)
        , Just bufType <- [resolveType env <$> Map.lookup x fields]
        , Just lenType <- [resolveType env <$> Map.lookup l fields]
        , count <- case c of
            Nothing -> [Nothing]
            Just g  -> [ Just (info (swap g) (Just (resolveType env t)) out) | t <- toList (Map.lookup g fields) ]
        ]
    outPaths =
        [ (info buf (Just bufType) True, info len (Just lenType) True, Nothing, bufType, lenType)
        | (b, l) <- outs
        , let buf = Path b [Deref]
              len = Path l [Deref]
        , Just bufType <- [deref . resolveType env <$> Map.lookup b (fcTypes ctx)]
        , Just lenType <- [deref . resolveType env <$> Map.lookup l (fcTypes ctx)]
        ]
    deref t = t { ctPointers = ctPointers t - 1 }
    infos = [ info p (exprType ctx e) (outlives e) | (e, p) <- named ]
        ++ concat [ b : l : toList c | (b, l, c, _, _) <- fieldPaths ++ outPaths ]
    pair ((bn, b), (ln, _), c, bufType, lenType) = Pair bn ln
        (case ctDims bufType of
            Range (Just n) _ : _ -> Just n
            _                    -> Nothing)
        (integerType env lenType) (piOutlives b) (fst <$> c) (c >>= piType . snd >>= integerType env)
    fieldPairs = map pair fieldPaths
    outPairs = map pair outPaths
    -- Through a pointer, or in a global.
    outlives (Fix n) = case n of
        PointerAccess{}        -> True
        UnaryExpr C.UopDeref _ -> True
        MemberAccess b _       -> outlives b
        ParenExpr b            -> outlives b
        ArrayAccess b _        -> maybe False (\t -> ctPointers t > 0 && null (ctDims t)) (resolveType env <$> exprType ctx b) || outlives b
        VarExpr (L _ _ v)      -> not (Set.member v own)
        _                      -> False

-- | The sizes of types a function may count bytes in that aren't one
-- number, with what they can be.
sizeSymbols :: FunctionCtx Text -> C.Node (Lexeme Text) -> [(Text, Range)]
sizeSymbols ctx body = nub
    [ (sizeofName t, r)
    | n <- subnodes body
    , t0 <- case unFix n of
        SizeofType ty       -> [typeOfDecl ty]
        SizeofExpr x        -> maybe [] pure (exprType ctx x)
        CastExpr _ x        -> maybe [] (pure . elementOf) (exprType ctx x)
        FunctionCall _ args -> [ elementOf t | a <- args, Just t <- [exprType ctx a] ]
        _                   -> []
    , let t = (resolveType env t0) { ctDims = [] }
          r = typeBytes env t
    , isNothing (exactSize r)
    , isJust (rLow r)
    ]
  where
    env = fcEnv ctx
    exactSize (Range (Just lo) (Just hi)) | lo == hi = Just lo
    exactSize _                                      = Nothing

-- | A function as what's known of other functions so far sees it. What it
-- needs of its parameters is assumed: every call is checked against it.
withSummaries :: Env -> Function -> Function
withSummaries env fn = fn
    { fnCtx = (fnCtx fn) { fcEnv = env }
    , fnInit = foldl' (flip addIneq) (foldl' narrowTo (fnStart fn)
        ([ (p, r) | (k, p) <- zip [0 ..] (fnArgs fn), Just r <- [Map.lookup k requires, Map.lookup k given] ]
         ++ [ (place, Range Nothing (Just most))
            | (k, most) <- Map.toList (Map.findWithDefault Map.empty (fnName fn) (envPointsAtMost env))
            , Just p <- [lookup k (zip [0 ..] (fnArgs fn))]
            , Just place <- [placeName (fnCtx fn) (Path p [Deref])] ]))
        ([ linVar (sizeName p) `linMinus` substitute named need
         | (k, needs) <- Map.toList (Map.findWithDefault Map.empty (fnName fn) (envNeeds env))
         , Just p <- [lookup k (zip [0 ..] (fnArgs fn))]
         , need <- needs ]
         ++ map (substitute named) (Map.findWithDefault [] (fnName fn) (envRelations env))
         ++ [ foldl' linPlus (linConstant (negate b)) terms
            | (g, b) <- Map.findWithDefault [] (fnName fn) (envGivenSums env)
            , Just terms <- [traverse own (Map.toList g)] ])
    }
  where
    requires = Map.findWithDefault Map.empty (fnName fn) (envRequires env)
    given = Map.findWithDefault Map.empty (fnName fn) (envGiven env)
    -- A place given as the function names it.
    own (ParamPlace k steps, n) = do
        p <- lookup k (zip [0 ..] (fnArgs fn))
        steps' <- argSteps (\j -> lookup j (zip [0 ..] (fnArgs fn))) steps
        linScale n . linVar <$> if null steps then Just p else placeName (fnCtx fn) (Path p steps')
    named v = maybe (linVar v) linVar (T.stripPrefix "#" v >>= readMaybe . T.unpack >>= \k -> lookup k (zip [0 :: Int ..] (fnArgs fn)))
    narrowTo fs (p, r) = case fs of
        Unreached -> Unreached
        _         -> setRange p (intersectRange r (Map.findWithDefault unknownRange p (fInts fs))) fs

-- | Whether a function does nothing with a pointer but store through it in
-- statements of their own, read through it and compare it with nullptr.
onlyStoredTo :: Text -> C.Node (Lexeme Text) -> Bool
onlyStoredTo p = go
  where
    go (Fix node) = case node of
        ExprStmt (Fix (AssignExpr lhs C.AopEq rhs)) | through lhs -> go rhs
        AssignExpr lhs _ _ | through lhs -> False
        UnaryExpr op x | op `elem` [C.UopIncr, C.UopDecr, C.UopAddress], through x -> False
        UnaryExpr C.UopDeref x | itself x -> True
        UnaryExpr C.UopNot x | itself x -> True
        BinaryExpr a op b | op `elem` [C.BopEq, C.BopNe], itself a && isNull b || isNull a && itself b -> True
        VarExpr (L _ _ v) -> v /= p
        _ -> all go node
    itself (Fix x) = case x of
        ParenExpr y       -> itself y
        VarExpr (L _ _ v) -> v == p
        _                 -> False
    through (Fix x) = case x of
        ParenExpr y            -> through y
        UnaryExpr C.UopDeref y -> itself y
        _                      -> False
    isNull (Fix x) = case x of
        LiteralExpr C.ConstId (L _ _ "nullptr") -> True
        _                                       -> False

-- | Variables a function assigns to, or passes the address of.
assignedVars :: C.Node (Lexeme Text) -> Set.Set Text
assignedVars (Fix node) = case node of
    AssignExpr (Fix (VarExpr (L _ _ v))) _ rhs       -> Set.insert v (assignedVars rhs)
    UnaryExpr C.UopIncr (Fix (VarExpr (L _ _ v)))    -> Set.singleton v
    UnaryExpr C.UopDecr (Fix (VarExpr (L _ _ v)))    -> Set.singleton v
    UnaryExpr C.UopAddress (Fix (VarExpr (L _ _ v))) -> Set.singleton v
    _                                                -> foldMap assignedVars node

-- | Names used other than as the function of a call: functions whose
-- callers can't all be seen.
usedAsValues :: C.Node (Lexeme Text) -> Set.Set Text
usedAsValues (Fix node) = case node of
    FunctionCall (Fix (VarExpr _)) args -> foldMap usedAsValues args
    VarExpr (L _ _ v)                   -> Set.singleton v
    _                                   -> foldMap usedAsValues node

analyse :: Function -> CFG Text Facts
analyse fn =
    let cfg = runIdentity (buildCFG (fnCtx fn) (fnDefn fn) (fnInit fn))
    in fst (runIdentity (fixpoint (fnCtx fn) (fnName fn) cfg))

-- | Facts before each statement of each block.
statementFacts :: Function -> CFG Text Facts -> [(Facts, C.Node (Lexeme Text))]
statementFacts fn cfg = concatMap block (Map.elems cfg)
  where
    block node = zip (scanl (transferStmt (fnCtx fn)) (cfgInFacts node) (cfgStmts node)) (cfgStmts node)

-- | How many elements a function's result has, from its return statements.
returnSize :: Function -> [(Facts, C.Node (Lexeme Text))] -> Maybe Integer
returnSize fn stmts =
    let sizes = [ size >>= lowerBound facts
                | (facts, Fix (Return (Just e))) <- stmts
                , facts /= Unreached
                , let size = sizeOf (fnCtx fn) facts e
                , size /= Just NullPointer ]
    in if null sizes then Nothing else minimum <$> sequence sizes

-- | Bounds of what a function returning an integer returns.
returnRange :: Function -> [(Facts, C.Node (Lexeme Text))] -> Maybe Range
returnRange fn stmts = case Map.lookup (fnName fn) (envFunctions env) >>= integerType env . sigReturn of
    Just t ->
        case [ returned facts t e | (facts, Fix (Return (Just e))) <- stmts, facts /= Unreached ] of
            []     -> Nothing
            r : rs -> Just (foldr hull r rs)
    Nothing -> Nothing
  where
    ctx = fnCtx fn
    env = fcEnv ctx
    -- Also what's known of how it relates to others (a count at most a
    -- loop's index).
    returned facts t e =
        let r = convertedRange ctx facts (Just t) e
        in maybe r (\l -> intersectRange r (rangeOfLin (typedFacts ctx facts l) l)) (convertedForm ctx facts (Just t) e)

-- | The integer parameters a function returning an integer returns at most
-- so much more than, when it doesn't return less than 0: the most over
-- every return that may not be. A parameter at its least plus so much
-- that's still all the type can hold says nothing.
returnAtMost :: Function -> Maybe (IntType, [(Facts, IntValue, IntValue)]) -> Map Int Integer
returnAtMost fn = returnAtMostBut fn (const False)

-- | The parameter (by position, one it doesn't change) a function returns
-- less than where it's at least 1, else 0: every return is a call that does
-- that of it ('callBelow').
returnBelow :: Function -> [(Facts, C.Node (Lexeme Text))] -> Maybe Int
returnBelow fn stmts = case nub [ below e | (fs, Fix (Return (Just e))) <- stmts, fs /= Unreached ] of
    [Just k] -> Just k
    _        -> Nothing
  where
    ctx = fnCtx fn
    below e = case e of
        Fix (ParenExpr x) -> below x
        Fix (FunctionCall f args) -> do
            j <- callBelow ctx f
            Fix (VarExpr (L _ _ p)) : _ <- Just (drop j args)
            Map.lookup p (fnParams fn)
        _ -> Nothing

-- | The least elements what a call through a pointer gives back has: of
-- every function the program gives as the pointer's type, if there are any
-- and each is known.
returnedThrough :: FunctionCtx Text -> C.Node (Lexeme Text) -> Maybe Integer
returnedThrough ctx f = do
    t <- exprType ctx f
    case targetsOf (fcSummaries ctx) (ctName (resolveType env t)) of
        [] -> Nothing
        gs -> minimum <$> traverse (`Map.lookup` envReturns env) gs
  where
    env = fcEnv ctx

-- | The argument (by position) a call returns less than where it's at
-- least 1, else 0 ('envBelow'): of a function, one the program doesn't
-- declare ('Platform.returnsBelow'), or every function a pointer it's made
-- through may be to.
callBelow :: FunctionCtx Text -> C.Node (Lexeme Text) -> Maybe Int
callBelow ctx f = case f of
    Fix (VarExpr (L _ _ name)) | not (Map.member name (fcTypes ctx)) -> case Map.lookup name (envBelow env) of
        Just k -> Just k
        Nothing | Map.notMember name (envFunctions env) -> Platform.returnsBelow name
        Nothing -> Nothing
    _ -> do
        t <- exprType ctx f
        case nub [ Map.lookup g (envBelow env) | g <- targetsOf (fcSummaries ctx) (ctName (resolveType env t)) ] of
            [Just k] -> Just k
            _        -> Nothing
  where
    env = fcEnv ctx

-- | The untouched of a function returning an unsigned integer, unless it
-- returns the most its type holds, if it may: what it returns for none.
returnAtMostUnless :: Function -> Maybe (IntType, [(Facts, IntValue, IntValue)]) -> Maybe (Integer, Map Int Integer)
returnAtMostUnless fn values0 = do
    (t, values) <- values0
    guard (not (itSigned t))
    k <- rHigh (itHolds t)
    guard (any (\(_, iv, _) -> ivRange iv == exactly k) values)
    let most = returnAtMostBut fn (== exactly k) values0
    (k, most) <$ guard (not (Map.null most))

-- | What 'returnAtMost' says, but of the returns of numbers in a range
-- that's left out.
returnAtMostBut :: Function -> (Range -> Bool) -> Maybe (IntType, [(Facts, IntValue, IntValue)]) -> Map Int Integer
returnAtMostBut fn but values0 = case values0 of
    Just (t, values) ->
        let returns = [ r | r@(_, iv, _) <- values, maybe True (>= 0) (rHigh (ivRange iv)), not (but (ivRange iv)) ]
            -- A number of at least 0 is at most what it was in any type.
            uppers facts iv v = upperForms facts iv ++ (if maybe False (>= 0) (rLow (ivRange v)) then upperForms facts v else [])
            more p (facts, iv, v) = case catMaybes [ upperLin facts (u `linMinus` linVar p) | u <- uppers facts iv v ] of
                [] -> Nothing
                ds -> Just (minimum ds)
        in if null returns then Map.empty else Map.fromList
            [ (k, d)
            | (p, k) <- Map.toList (fnParams fn)
            , Just pt <- [Map.lookup p (fcTypes ctx) >>= integerType env]
            , Just d <- [maximum <$> traverse (more p) returns]
            , Just lo <- [rLow (itHolds pt)]
            , Just hi <- [rHigh (itCanHold t)]
            , lo + d < hi
            ]
    Nothing -> Map.empty
  where
    ctx = fnCtx fn
    env = fcEnv ctx

-- | Integer places fields and pointers lead to from the pointer parameters
-- a function doesn't change, and how much more than each it returns at
-- most, at every return.
returnAtMostPlaces :: Function -> Maybe (IntType, [(Facts, IntValue, IntValue)]) -> Map ParamPlace Integer
returnAtMostPlaces fn values0 = case values0 of
    Just (_, values) ->
        let returns = [ (facts, iv) | (facts@Facts{}, iv, _) <- values ]
            more v (facts0, iv) = let facts = withRange ctx v facts0 in case catMaybes [ upperLin facts (u `linMinus` linVar v) | u <- upperForms facts iv ] of
                [] -> Nothing
                ds -> Just (minimum ds)
        in if null returns then Map.empty else Map.fromList
            [ (ParamPlace k steps', d)
            | (v, info) <- Map.toList (fcPaths ctx)
            , let Path root steps = piPath info
            , Just k <- [Map.lookup root (fnParams fn)]
            , not (null steps)
            , Just steps' <- [paramSteps (fnParams fn) steps]
            , isJust (piType info >>= integerType env)
            , Just d <- [maximum <$> traverse (more v) returns]
            ]
    Nothing -> Map.empty
  where
    ctx = fnCtx fn
    env = fcEnv ctx

-- | What a function returns below 0, if it otherwise returns only numbers
-- of at least 0 converted to its type.
returnFailures :: Maybe (IntType, [(Facts, IntValue, IntValue)]) -> Maybe [Range]
returnFailures values0 = do
    (_, values) <- values0
    let failure (_, iv, v)
            | maybe False (< 0) (rHigh (ivRange iv)) = Just [ivRange iv]
            | maybe False (>= 0) (rLow (ivRange v)) = Just []
            | otherwise = Nothing
    nub . concat <$> traverse failure values

-- | What each return of a function returning an integer gives: in the
-- function's type, and before it's converted to it.
returnValues :: Function -> [(Facts, C.Node (Lexeme Text))] -> Maybe (IntType, [(Facts, IntValue, IntValue)])
returnValues fn stmts = do
    t <- Map.lookup (fnName fn) (envFunctions env) >>= integerType env . sigReturn
    return (t, [ (facts, convertValue ctx facts (Just t) v, v)
               | (facts, Fix (Return (Just e))) <- stmts
               , facts /= Unreached
               , let v = intValue ctx facts e ])
  where
    ctx = fnCtx fn
    env = fcEnv ctx

-- | What is put in each pointer field, and how many elements it has: of
-- unknown size if it's changed some other way, or through its address.
-- Also what initialisers give them.
fieldStores :: Function -> [(Facts, C.Node (Lexeme Text))] -> [((Text, Text), Maybe Integer)]
fieldStores fn stmts =
    [ (key, size)
    | (facts, stmt) <- stmts
    , facts /= Unreached
    , (key, mRhs) <- [ (key, mRhs)
                     | (lhs, mRhs) <- concatMap writes (statementExprs stmt)
                     , Just key <- [fieldKey ctx lhs]
                     , maybe False (\t -> ctPointers t > 0 && null (ctDims t)) (exprType ctx lhs) ]
                  ++ concat [ initialiserFields (fcEnv ctx) ty ini | (ty, ini) <- concatMap initialised (statementExprs stmt) ]
    , let rhsSize = mRhs >>= sizeOf ctx facts
    , rhsSize /= Just NullPointer
    , let size = rhsSize >>= lowerBound facts
    ]
  where
    ctx = fnCtx fn
    -- An array's initialiser isn't followed.
    initialised (Fix node) = case node of
        VarDeclStmt (Fix (VarDecl ty _ dims)) (Just ini@(Fix InitialiserList{})) -> [(typeOfDecl ty, ini <$ guard (null dims))]
        CompoundLiteral ty ini@(Fix InitialiserList{}) -> [(typeOfDecl ty, Just ini)]
        _ -> []
    writes (Fix node) = case node of
        AssignExpr lhs C.AopEq rhs -> [(lhs, Just rhs)]
        AssignExpr lhs _ _         -> [(lhs, Nothing)]
        UnaryExpr C.UopIncr x      -> [(x, Nothing)]
        UnaryExpr C.UopDecr x      -> [(x, Nothing)]
        UnaryExpr C.UopAddress x   -> [(x, Nothing)]
        _                          -> []

-- | What each integer field a function changes is given: what's stored,
-- or what it was moved from by a sum, else anything its type holds. What's
-- no more than the field already was (and doesn't wrap round), such as a
-- count taken down where it isn't 0, keeps it in what it's given anyway:
-- only how low it goes counts. With each, what it's hoped to be: an
-- unsigned field taken down from itself, as if that doesn't wrap round.
fieldRanges :: Function -> [(Facts, C.Node (Lexeme Text))] -> [((Text, Text), Range, Range)]
fieldRanges fn stmts =
    [ (key, actual, if takenDown facts lhs value && rLow (itCanHold t) == Just 0 then exactly 0 else actual)
    | (facts, stmt) <- stmts
    , facts /= Unreached
    , (lhs, value) <- concatMap stored (statementExprs stmt)
    , Just key <- [fieldKey ctx lhs]
    , Just t <- [exprType ctx lhs >>= integerType (fcEnv ctx)]
    , let actual = maybe (itCanHold t) (given facts lhs . convertValue ctx facts (Just t) . intValue ctx facts) value
    ]
  where
    takenDown facts lhs = \case
        Just (Fix (BinaryExpr x C.BopMinus k)) -> isJust (pathOf lhs) && pathOf x == pathOf lhs && maybe False (>= 0) (rLow (rangeOf ctx facts k))
        _ -> False
    ctx = fnCtx fn
    stored (Fix node) = case node of
        AssignExpr lhs C.AopEq rhs    -> [(lhs, Just rhs)]
        AssignExpr lhs C.AopPlus rhs  -> [(lhs, Just (Fix (BinaryExpr lhs C.BopPlus rhs)))]
        AssignExpr lhs C.AopMinus rhs -> [(lhs, Just (Fix (BinaryExpr lhs C.BopMinus rhs)))]
        AssignExpr lhs _ _            -> [(lhs, Nothing)]
        UnaryExpr C.UopIncr x         -> [(x, Just (Fix (BinaryExpr x C.BopPlus one)))]
        UnaryExpr C.UopDecr x         -> [(x, Just (Fix (BinaryExpr x C.BopMinus one)))]
        UnaryExpr C.UopAddress x      -> [(x, Nothing)]
        _                             -> []
    one = Fix (LiteralExpr C.Int (L (C.AlexPn 0 0 0) C.LitInteger "1"))
    given facts lhs iv
        | Just (n, _) <- trackedPath ctx lhs
        , Just l <- exactForm iv
        , maybe False (>= 0) (lowerLin facts (linVar n `linMinus` l))
        , Just lo <- rLow (ivRange iv) = exactly lo
        | otherwise = ivRange iv

-- | Unions, and the structs given something but zeros where they're made:
-- what any of their fields is may be anything.
initialisedWith :: Env -> C.Node (Lexeme Text) -> [Text]
initialisedWith env (Fix node) = case node of
    Union (L _ _ name) _ -> name : rest
    VarDeclStmt (Fix (VarDecl ty _ _)) (Just e) -> given (typeOfDecl ty) e ++ rest
    ConstDefn _ ty _ e -> given (typeOfDecl ty) e ++ rest
    CompoundLiteral ty e -> given (typeOfDecl ty) e ++ rest
    _ -> rest
  where
    rest = concatMap (initialisedWith env) (toList node)
    given ty e
        | allZero e = []
        | otherwise = [ ctName t | let t = resolveType env ty, ctPointers t == 0, Map.member (ctName t) (envStructs env) ]
    allZero (Fix e) = case e of
        InitialiserList es                      -> all allZero es
        LiteralExpr C.Int (L _ _ "0")           -> True
        LiteralExpr C.ConstId (L _ _ "nullptr") -> True
        LiteralExpr C.Bool (L _ _ "false")      -> True
        _                                       -> False

-- | A statement's expressions, all the way down, but not the statements
-- inside it: those are their own CFG nodes.
statementExprs :: C.Node (Lexeme Text) -> [C.Node (Lexeme Text)]
statementExprs n@(Fix node) = n : case node of
    IfStmt c _ _    -> statementExprs c
    WhileStmt c _   -> statementExprs c
    DoWhileStmt _ c -> statementExprs c
    ForStmt i _ _ _ -> statementExprs i
    SwitchStmt c _  -> statementExprs c
    CompoundStmt _  -> []
    _               -> concatMap statementExprs (toList node)

-- | Struct fields given values by initialisers outside functions, which
-- aren't followed: the pointer fields of the struct and of the structs in
-- it.
initialisedFields :: Env -> C.Node (Lexeme Text) -> [(Text, Text)]
initialisedFields env (Fix node) = case node of
    FunctionDefn{} -> []
    VarDeclStmt (Fix (VarDecl ty _ _)) (Just ini@(Fix InitialiserList{})) -> given (typeOfDecl ty) ini ++ rest
    CompoundLiteral ty ini -> given (typeOfDecl ty) ini ++ rest
    _ -> rest
  where
    rest = concatMap (initialisedFields env) (toList node)
    given ty ini = [ key | not (zeroInitialiser ini), (key, _) <- initialiserFields env ty Nothing ]

-- | The pointer fields of a struct an initialiser gives values, by struct
-- and field, with what each is given where that can be told: by the order
-- the fields are declared in, through the structs in it given their own.
-- Zeros make a pointer nullptr, which says nothing of a size. Fields not
-- given anything are zeros.
initialiserFields :: Env -> CType -> Maybe (C.Node (Lexeme Text)) -> [((Text, Text), Maybe (C.Node (Lexeme Text)))]
initialiserFields env ty = go Set.empty (resolveType env ty)
  where
    go seen t mIni
        | ctPointers t > 0 || Set.member (ctName t) seen = []
        | Just ini <- mIni, zeroInitialiser ini = []
        | Just (Fix (InitialiserList es)) <- mIni
        , Just order <- Map.lookup (ctName t) (envFieldOrder env)
        , Just fields <- Map.lookup (ctName t) (envStructs env) = concat
            [ if ctPointers ft > 0 && null (ctDims ft) then [((ctName t, f), Just e)]
              else go (Set.insert (ctName t) seen) ft { ctDims = [] } (e <$ guard (null (ctDims ft)))
            | (f, e) <- zip order es
            , Just ft <- [resolveType env <$> Map.lookup f fields]
            ]
        | otherwise = concat
            [ if ctPointers ft > 0 && null (ctDims ft) then [((ctName t, f), Nothing)] else go (Set.insert (ctName t) seen) ft { ctDims = [] } Nothing
            | (f, ft0) <- maybe [] Map.toList (Map.lookup (ctName t) (envStructs env))
            , let ft = resolveType env ft0
            ]

-- | Pairs that outlive a function and can't be shown to hold where it ends
-- without a return statement.
endFailures :: Function -> CFG Text Facts -> [Failure]
endFailures fn cfg =
    [ fl
    | node <- Map.elems cfg
    , any (`Set.member` exits) (cfgSuccs node)
    , not (endsInReturn (cfgStmts node))
    , fl <- checkPairs ctx (foldl' (transferStmt ctx) (cfgInFacts node) (cfgStmts node)) (fcLoc ctx)
        (filter prOutlives (fcPairs ctx))
    ]
  where
    ctx = fnCtx fn
    exits = Set.fromList [ cfgNodeId node | node <- Map.elems cfg, null (cfgSuccs node), null (cfgStmts node) ]
    endsInReturn stmts = case reverse stmts of
        Fix Return{} : _ -> True
        _                -> False

-- | Needs without those another one covers: the untouched sum with a bigger
-- number.
pruneNeeds :: [Lin] -> [Lin]
pruneNeeds needs = nub [ n | n <- needs, not (any (covers n) needs) ]
  where
    covers n m = linVars m == linVars n && linConst m > linConst n

-- | What fails in a function where something can't be shown, if anything is
-- worked out from it: what it needs of its callers.
summaryFailures :: Function -> [(Facts, C.Node (Lexeme Text))] -> [Failure]
summaryFailures fn stmts
    | fnClosed fn || fnDirect fn = concat [ checkStmt (fnCtx fn) facts stmt | (facts, stmt) <- stmts ]
    | otherwise = []

-- | The symbol for how many elements a buffer parameter has.
sizeName :: Text -> Text
sizeName p = "size(" <> p <> ")"

-- | What a function every call to which is by its name needs of the buffers
-- it's given: what its calls need of one, less what it's taken off it, in
-- the parameters it doesn't change.
needsOf :: Function -> [Failure] -> Map Int [Lin]
needsOf fn failures
    | not (fnDirect fn) = Map.empty
    | otherwise = Map.map pruneNeeds $ Map.fromListWith (++)
        [ (k, [need'])
        | fl <- failures
        , Just (size, needed) <- [flDeficit fl]
        , (k, p) <- zip [0 ..] (fnArgs fn)
        , Map.lookup (sizeName p) (linVars size) == Just 1
        , let need = needed `linMinus` (size `linMinus` linVar (sizeName p))
        , Just need' <- [byPosition fn need]
        ]

-- | A sum of a function's parameters, by their positions (@#k@).
byPosition :: Function -> Lin -> Maybe Lin
byPosition fn (Lin vars c) = (`Lin` c) . Map.fromList <$> traverse (\(v, n) -> (\k -> ("#" <> T.pack (show k), n)) <$> Map.lookup v (fnParams fn)) (Map.toList vars)

-- | Where a function returning @bool@ may return true, what its integer
-- parameters it doesn't change are: of each, what all those places allow.
trueRanges :: Function -> [(Facts, C.Node (Lexeme Text))] -> Maybe (Map Int Range)
trueRanges fn stmts = do
    trues <- trueFacts fn stmts
    return $ Map.filter (/= unknownRange) $ Map.fromList
        [ (k, foldr1 hull [ placeRange (fnCtx fn) p fs | fs <- trues ])
        | (p, k) <- Map.toList (fnParams fn) ]

-- | What's known where a function returning @bool@ returns true, if it
-- may: what it returns holds there.
trueFacts :: Function -> [(Facts, C.Node (Lexeme Text))] -> Maybe [Facts]
trueFacts fn stmts = do
    sig <- Map.lookup (fnName fn) (envFunctions env)
    guard (resolveType env (sigReturn sig) == CType "bool" 0 [])
    let trues = [ fs' | (fs, Fix (Return (Just e))) <- stmts, fs /= Unreached, rangeOf ctx fs e /= exactly 0
                      , let fs' = narrow ctx True e fs, fs' /= Unreached ]
    trues <$ guard (not (null trues))
  where
    ctx = fnCtx fn
    env = fcEnv ctx

-- | Sums of what a function is given that it has made sure of where it
-- says it did what it was asked ('succeededFacts'): of the integer
-- parameters it doesn't change, and of places fields and pointers lead to
-- from the pointer parameters it doesn't change, as they are when it
-- returns. Each with the least it is at all those places.
madeSums :: Function -> [(Facts, C.Node (Lexeme Text))] -> Maybe [(Map ParamPlace Integer, Integer)]
madeSums fn stmts = do
    succeeded <- succeededFacts fn stmts
    let sums = Set.toList $ Set.fromList
            [ g | Facts{fIneqs = ineqs} <- succeeded, g <- Map.keys ineqs, all (isJust . paramPlace fn) (Map.keys g) ]
    return
        [ (placed, minimum bounds)
        | g <- sums
        , Just bounds <- [traverse (\fs -> lowerLin fs (Lin g 0)) succeeded]
        , Just placed <- [Map.fromList <$> traverse (\(v, n) -> (\pl -> (pl, n)) <$> paramPlace fn v) (Map.toList g)]
        ]

-- | What a function leaves the integer places fields and pointers lead to
-- from the pointer parameters it doesn't change at, wherever it ends (past
-- what a return evaluates): of each, what all those places allow.
leavesOf :: Function -> CFG Text Facts -> [(Facts, C.Node (Lexeme Text))] -> Map ParamPlace Range
leavesOf fn cfg stmts = Map.fromList
    [ (pl, r)
    | not (null ends)
    , (n, info) <- Map.toList (fcPaths ctx)
    , Just t <- [piType info >>= integerType env]
    , Just pl@(ParamPlace _ (_ : _)) <- [paramPlace fn n]
    , let r = foldr1 hull [ placeRange ctx n fs | fs <- ends ]
    , r /= itCanHold t
    , r /= unknownRange
    ]
  where
    ctx = fnCtx fn
    env = fcEnv ctx
    ends = filter (/= Unreached) $
        [ transferStmt ctx fs stmt | (fs, stmt@(Fix Return{})) <- stmts, fs /= Unreached ]
        ++ [ foldl' (transferStmt ctx) (cfgInFacts node) (cfgStmts node)
           | node <- Map.elems cfg
           , any (`Set.member` exits) (cfgSuccs node)
           , case reverse (cfgStmts node) of
               Fix Return{} : _ -> False
               _                -> True
           ]
    exits = Set.fromList [ cfgNodeId node | node <- Map.elems cfg, null (cfgSuccs node), null (cfgStmts node) ]

-- | What the integers the pointers a function only stores to point to are
-- where it says it did what it was asked ('succeededFacts'): of each, what
-- all those places allow.
madeStores :: Function -> [(Facts, C.Node (Lexeme Text))] -> Map Int Range
madeStores fn stmts = fromMaybe Map.empty $ do
    succeeded <- succeededFacts fn stmts
    return $ Map.filter (/= unknownRange) $ Map.fromList
        [ (k, foldr1 hull [ placeRange (fnCtx fn) name fs | fs <- succeeded ])
        | (p, k) <- Map.toList (fnStores fn)
        , Just name <- [placeName (fnCtx fn) (Path p [Deref])]
        ]

-- | A parameter the function doesn't change, or a place fields and
-- pointers lead to from one, by the parameter's position.
paramPlace :: Function -> Text -> Maybe ParamPlace
paramPlace fn v = case Map.lookup v (fnParams fn) of
    Just k -> Just (ParamPlace k [])
    Nothing -> do
        Path root steps <- piPath <$> Map.lookup v (fcPaths (fnCtx fn))
        k <- Map.lookup root (fnParams fn)
        ParamPlace k <$> paramSteps (fnParams fn) steps

-- | What's known where a function says it did what it was asked: where it
-- returns true, for one returning @bool@, or 0, for one returning an
-- integer.
succeededFacts :: Function -> [(Facts, C.Node (Lexeme Text))] -> Maybe [Facts]
succeededFacts fn stmts = do
    sig <- Map.lookup (fnName fn) (envFunctions env)
    if resolveType env (sigReturn sig) == CType "bool" 0 [] then trueFacts fn stmts else do
        _ <- integerType env (sigReturn sig)
        let zeros = [ fs'
                    | (fs, Fix (Return (Just e))) <- stmts, fs /= Unreached, exactly 0 `within` rangeOf ctx fs e
                    , let fs' = narrow ctx True (Fix (BinaryExpr e C.BopEq zero)) fs, fs' /= Unreached ]
        zeros <$ guard (not (null zeros))
  where
    ctx = fnCtx fn
    env = fcEnv ctx
    zero = Fix (LiteralExpr C.Int (L (C.AlexPn 0 0 0) C.LitInteger "0"))

-- | The buffers fields and pointers lead to from the pointer parameters a
-- function doesn't change, and how many elements it has made each have
-- where it says it did ('succeededFacts'): a sum of the integer parameters
-- it doesn't change that each has at least everywhere it says so, or is at
-- most 0 where it's nullptr.
madeSizes :: Function -> [(Facts, C.Node (Lexeme Text))] -> Map ParamPlace Lin
madeSizes fn stmts = fromMaybe Map.empty $ do
    succeeded <- succeededFacts fn stmts
    let candidates = Map.fromListWith (++)
            [ (n, [base])
            | fs <- succeeded
            , n <- Map.keys (fcPaths (fnCtx fn))
            , Just (Size base) <- [sizeAt fs n]
            , isJust (byPosition fn base)
            -- None says nothing.
            , not (Map.null (linVars base)) || linConst base > 0
            ]
    return $ Map.fromList
        [ (pl, l')
        | (n, ls) <- Map.toList candidates
        , Just pl <- [paramPlace fn n]
        , l : _ <- [filter (\l -> all (holds n l) succeeded) (nub ls)]
        , Just l' <- [byPosition fn l]
        ]
  where
    -- A buffer from where it starts.
    sizeAt fs n = case fs of
        Facts{fPointers = ps, fInts = is}
            | Just (Pointer _ size) <- Map.lookup n ps
            , Map.lookup (offsetVar n) is == Just (exactly 0) -> Just size
        _ -> Nothing
    holds n l fs = case sizeAt fs n of
        Just (Size s)    -> maybe False (>= 0) (lowerLin fs (s `linMinus` l))
        Just NullPointer -> maybe False (<= 0) (upperLin fs l)
        Nothing          -> False

-- | What a function every call to which is by its name needs of how its
-- integer parameters relate: what's short, when it's a sum of more than one
-- of them (or one so many times), must be at least 0.
relationsOf :: Function -> [Failure] -> [Lin]
relationsOf fn failures = nub
    [ rel
    | fnDirect fn
    , fl <- failures
    , Just (size, needed) <- [flDeficit fl]
    , let short@(Lin vars _) = size `linMinus` needed
    , case Map.elems vars of
        []  -> False
        [n] -> abs n /= 1
        _   -> True
    , Just rel <- [byPosition fn short]
    ]

-- | What a function needs of the integer parameters it doesn't change: of
-- a closed one, the least each must be for its calls to be big enough; of
-- one every call to which is by its name, the bounds on one parameter that
-- what's short comes to.
requirementsOf :: Function -> [Failure] -> Map Int Range
requirementsOf fn failures = Map.fromListWith intersectRange (least ++ bounds)
  where
    least =
        [ (k, Range (Just r) Nothing)
        | fnClosed fn
        , fl <- failures
        , Just (v, r) <- [flRequirement fl]
        , Just k <- [Map.lookup v (fnParams fn)]
        ]
    -- What's short is at least 0: n * v + c >= 0.
    bounds =
        [ (k, if n > 0 then Range (Just (negate c)) Nothing else Range Nothing (Just c))
        | fnDirect fn
        , fl <- failures
        , Just (size, needed) <- [flDeficit fl]
        , let Lin vars c = size `linMinus` needed
        , [(v, n)] <- [Map.toList vars]
        , abs n == 1
        , Just k <- [Map.lookup v (fnParams fn)]
        ]

-- | What a function every call to which is by its name needs of what the
-- pointers to integers it only stores to point to where it starts: of one
-- it starts a local as, the most that local can be where it's first used
-- for what a buffer of a fixed size has room for.
pointeeRequirements :: Function -> [Failure] -> Map Int Integer
pointeeRequirements fn failures = Map.fromListWith min
    [ (k, most - c)
    | fnDirect fn
    , fl <- failures
    , Just (Lin sizeVars most, Lin vars c) <- [flDeficit fl]
    , Map.null sizeVars
    , [(v, 1)] <- [Map.toList vars]
    , Just k <- [Map.lookup v (fnCopies fn)]
    ]

-- | What a function's calls to static functions whose every caller can be
-- seen give their integer parameters (by position).
givenTo :: Function -> [(Facts, C.Node (Lexeme Text))] -> Map Text (Map Int Range)
givenTo fn stmts = Map.fromListWith (Map.unionWith hull)
    [ (name, Map.fromList [ (k, convertedRange ctx fs (Just t) arg)
                          | (k, Just param, arg) <- zip3 [0 ..] (sigParams sig ++ repeat Nothing) args
                          , Just t <- [integerType env (paramType param)] ])
    | (facts, stmt) <- stmts
    -- The condition was evaluated where it's made, not in each branch.
    , not (isBranch stmt)
    , (fs, (f, args)) <- callsWithFacts ctx facts stmt
    , Just (name, sig) <- [signatureOf ctx f]
    , Set.member name (envClosed env)
    ]
  where
    ctx = fnCtx fn
    env = fcEnv ctx
    isBranch (Fix (ExprStmt (Fix (FunctionCall (Fix (VarExpr (L _ _ f))) _)))) = "__tokstyle_assume_" `T.isPrefixOf` f
    isBranch _ = False

-- | Sums of what the calls a function makes to each of those give it,
-- known to be at least a bound where all of them are made: what's known of
-- the caller's variables and places, in terms of the parameters (an
-- integer argument that's a variable plus a constant) and places fields
-- and pointers lead to from them (a pointer argument with a path).
givenSumsTo :: Function -> [(Facts, C.Node (Lexeme Text))] -> Map Text (Map (Map ParamPlace Integer) Integer)
givenSumsTo fn stmts = Map.fromListWith (Map.intersectionWith min)
    [ (name, sumsAt fs sig args)
    | (facts, stmt) <- stmts
    , not (isBranch stmt)
    , (fs@Facts{}, (f, args)) <- callsWithFacts ctx facts stmt
    , Just (name, sig) <- [signatureOf ctx f]
    , Set.member name (envClosed env)
    ]
  where
    ctx = fnCtx fn
    env = fcEnv ctx
    isBranch (Fix (ExprStmt (Fix (FunctionCall (Fix (VarExpr (L _ _ f))) _)))) = "__tokstyle_assume_" `T.isPrefixOf` f
    isBranch _ = False
    sumsAt fs sig args =
        let given = concat (zipWith3 (placesGiven fs args) [0 ..] (sigParams sig ++ repeat Nothing) args)
            places = Map.fromList given
            -- Places given the same variable are the same.
            alike =
                [ (Map.fromList [(pa, 1), (pb, -1)], db - da)
                | ps <- Map.elems (Map.fromListWith (++) [ (v, [p]) | (v, p) <- given ])
                , (pa, da) <- ps
                , (pb, db) <- ps
                , pa /= pb
                ]
        in Map.fromListWith max $ alike ++
            [ (placed, b - sum [ n * d | (v, n) <- Map.toList g, Just (_, d) <- [Map.lookup v places] ])
            | (g, b) <- Map.toList (fIneqs fs)
            , Just placed <- [Map.filter (/= 0) . Map.fromListWith (+) <$> traverse (\(v, n) -> (\(pl, _) -> (pl, n)) <$> Map.lookup v places) (Map.toList g)]
            , not (Map.null placed)
            ]
    -- The caller's variables and places an argument is, with how much more
    -- than the parameter each is.
    placesGiven fs args k param arg = case integerType env . paramType =<< param of
        Just t
            | let iv = intValue ctx fs arg
            , keepsValue (ivType iv) (Just t) (ivRange iv)
            , Just (Lin vars c) <- exactForm iv
            , [(v, 1)] <- Map.toList vars -> [(v, (ParamPlace k [], negate c))]
            | otherwise -> []
        Nothing -> case pointedAt arg of
            Just (q, through) ->
                [ (n, (ParamPlace k rest', 0))
                | (n, info) <- Map.toList (fcPaths ctx)
                , let p = piPath info
                , pathRoot p == pathRoot q
                , pathSteps q `isPrefixOf` pathSteps p
                , let rest = through ++ drop (length (pathSteps q)) (pathSteps p)
                , not (null rest)
                , Just rest' <- [paramSteps (Map.fromList (reverse [ (i, j) | (j, Fix (VarExpr (L _ _ i))) <- zip [0 ..] args ])) rest]
                ]
            Nothing -> []
    -- What an argument is a path to, and what's added to go through it: a
    -- pointer to one place goes to that place.
    pointedAt arg = case arg of
        Fix (VarExpr (L _ _ v)) | Just place <- Map.lookup v (fcAliases ctx) -> Just (place, [Deref])
        _ -> (\q -> (q, [])) <$> pathOf arg

-- | What a function stores through the pointers to integers it only stores
-- to: the bounds of the values, and how much more than each integer
-- parameter it doesn't change they are at most.
storedThrough :: Function -> [(Facts, C.Node (Lexeme Text))] -> Map Int (Range, Map Int Integer)
storedThrough fn stmts = Map.fromList
    [ (k, (foldr1 hull [ ivRange iv | (_, iv) <- stores ], Map.fromList (mapMaybe (more stores) (Map.toList (fnParams fn)))))
    | (p, k) <- Map.toList (fnStores fn)
    , Just t <- [Map.lookup p (fcTypes ctx) >>= \ty -> integerType env (resolveType env ty) { ctPointers = 0 }]
    , let stores = [ (fs, convertValue ctx fs (Just t) (intValue ctx fs rhs))
                   | (fs, Fix (ExprStmt (Fix (AssignExpr lhs C.AopEq rhs)))) <- stmts
                   , fs /= Unreached
                   , through p lhs
                   ]
    , not (null stores)
    ]
  where
    ctx = fnCtx fn
    env = fcEnv ctx
    more stores (q, k) = do
        _ <- Map.lookup q (fcTypes ctx) >>= integerType env
        ds <- traverse (\(fs, iv) -> least (catMaybes [ upperLin fs (u `linMinus` linVar q) | u <- upperForms fs iv ])) stores
        return (k, maximum ds)
    least [] = Nothing
    least ds = Just (minimum ds)
    through q (Fix x) = case x of
        ParenExpr y                                    -> through q y
        UnaryExpr C.UopDeref (Fix (VarExpr (L _ _ v))) -> v == q
        _                                              -> False

-- | What calls store through pointers to integers they're given, of ones
-- that do nothing else with them: what was there, or what they store. Only
-- for a place nothing else in the statement may change, with bounds in
-- terms of what the calls don't change.
givenBack :: FunctionCtx Text -> Facts -> [Call] -> [C.Node (Lexeme Text)] -> Facts -> Facts
givenBack _ Unreached _ _ facts = facts
givenBack ctx before calls exprs facts = foldl' put facts
    [ (n, values) | (n, values) <- Map.toList stored, n `notElem` elsewhere, taken n == length [ () | (_, _, n', True, _) <- given, n' == n ] ]
  where
    env = fcEnv ctx
    given =
        [ (i, k, n, isAddress arg, (r, [ linPlus u (linConstant d) | (j, d) <- Map.toList most, Just u <- [argForm sig args j] ]))
        | (i, (f, args)) <- zip [0 :: Int ..] calls
        , Just (name, sig) <- [signatureOf ctx f]
        , (k, (r, most)) <- Map.toList (Map.findWithDefault Map.empty name (envStores env))
        , Just arg <- [lookup k (zip [0 ..] args)]
        , Just n <- [outTarget ctx arg]
        ]
    stored = Map.fromListWith (\(r1, u1) (r2, u2) -> (hull r1 r2, filter (`elem` u2) u1)) [ (n, v) | (_, _, n, _, v) <- given ]
    -- What the calls may change through their other arguments.
    others = [ (f, [ a | (k, a) <- zip [0 ..] args, (i, k) `notElem` [ (i', k') | (i', k', _, _, _) <- given ] ]) | (i, (f, args)) <- zip [0 ..] calls ]
    elsewhere = callsReach ctx others ++ writtenThrough ctx others
    changed = callsReach ctx calls ++ writtenThrough ctx calls
    taken n = length [ () | Fix (UnaryExpr C.UopAddress x) <- exprs, placeOf ctx x == Just n ]
    isAddress (Fix x) = case x of
        ParenExpr y              -> isAddress y
        UnaryExpr C.UopAddress _ -> True
        _                        -> False
    argForm sig args j = do
        arg <- lookup j (zip [0 ..] args)
        let t = case drop j (sigParams sig) of
                Just param : _ -> integerType env (paramType param)
                _              -> Nothing
        convertedForm ctx before t arg
    put fs (n, (r, uppers)) =
        let old = placeRange ctx n before
            kept = [ u | u <- uppers
                       , not (any (`elem` (n : changed)) (Map.keys (linVars u)))
                       , maybe False (>= 0) (lowerLin before (u `linMinus` linVar n)) ]
        in foldl' (\acc u -> addIneq (u `linMinus` linVar n) acc) (setRange n (intersectRange (hull old r) (placeRange ctx n fs)) fs) kept

-- | Functions called where not every call can be seen: in a macro (made
-- wherever it's used), or outside a function.
calledUnseen :: C.Node (Lexeme Text) -> Set.Set Text
calledUnseen = go False
  where
    go inFunction n@(Fix node) = case node of
        FunctionDefn _ _ body -> go True body
        PreprocDefineMacro{} -> callees n
        PreprocDefineConst{} -> callees n
        FunctionCall (Fix (VarExpr (L _ _ f))) args | not inFunction -> Set.insert f (foldMap (go inFunction) args)
        _ -> foldMap (go inFunction) node
    callees n = Set.fromList [ f | Fix (FunctionCall (Fix (VarExpr (L _ _ f))) _) <- subnodes n ]

-- | Functions a function calls in statements its graph doesn't have.
calledOffGraph :: Analysed -> Set.Set Text
calledOffGraph Analysed{anFunction = fn, anCfg = cfg} = Set.fromList [ f | (pos, f) <- callsOf [fnDefn fn], not (Set.member (pos, f) inGraph) ]
  where
    inGraph = Set.fromList (callsOf (concatMap cfgStmts (Map.elems cfg)))
    callsOf nodes = [ (pos, f) | n <- nodes, Fix (FunctionCall (Fix (VarExpr (L (C.AlexPn pos _ _) _ f))) _) <- subnodes n ]

-- | One report for each place signed arithmetic may overflow, of the most
-- it may be: a statement can be in the graph more than once.
overflowsOnce :: [Failure] -> [Failure]
overflowsOnce fls = Map.elems (Map.fromListWith widest [ (flLoc fl, fl) | fl <- fls ])
  where
    widest a b = case (flKind a, flKind b) of
        (Overflows alo ahi least most, Overflows blo bhi _ _) ->
            a { flKind = Overflows (min <$> alo <*> blo) (max <$> ahi <*> bhi) least most }
        _ -> a

-- | A function worked out with the summaries as they were: the graph with
-- its facts, the facts before each statement, and what it tells of the
-- function.
data Analysed = Analysed
    { anFunction :: Function
    , anCfg      :: CFG Text Facts
    , anFacts    :: [(Facts, C.Node (Lexeme Text))]
    , anSummary  :: Summary
    }

data Summary = Summary
    { suSize         :: Maybe Integer
    , suRange        :: Maybe Range
    , suAtMost       :: Map Int Integer
    , suAtMostUnless :: Maybe (Integer, Map Int Integer)
    , suBelow        :: Maybe Int
    , suAtMostPlaces :: Map ParamPlace Integer
    , suFailures     :: Maybe [Range]
    , suStores       :: [((Text, Text), Maybe Integer)]
    , suFields       :: [((Text, Text), Range, Range)]
    , suRequires     :: Map Int Range
    , suPointsAtMost :: Map Int Integer
    , suNeeds        :: Map Int [Lin]
    , suRelations    :: [Lin]
    , suTrue         :: Maybe (Map Int Range)
    , suMadeSums     :: Maybe [(Map ParamPlace Integer, Integer)]
    , suMadeSizes    :: Map ParamPlace Lin
    , suMadeStores   :: Map Int Range
    , suLeaves       :: Map ParamPlace Range
    , suGives        :: Map Text (Map Int Range)
    , suGivesSums    :: Map Text (Map (Map ParamPlace Integer) Integer)
    , suOut          :: Map Int (Range, Map Int Integer)
    }

analysedWith :: Env -> Function -> Analysed
analysedWith env fn0 =
    let fn = withSummaries env fn0
        cfg = analyse fn
        stmts = statementFacts fn cfg
        failures = summaryFailures fn stmts
        values = returnValues fn stmts
    in Analysed fn cfg stmts Summary
        { suSize = returnSize fn stmts
        , suRange = returnRange fn stmts
        , suAtMost = returnAtMost fn values
        , suAtMostUnless = returnAtMostUnless fn values
        , suBelow = returnBelow fn stmts
        , suAtMostPlaces = returnAtMostPlaces fn values
        , suFailures = returnFailures values
        , suStores = fieldStores fn stmts
        , suFields = fieldRanges fn stmts
        , suRequires = requirementsOf fn failures
        , suPointsAtMost = pointeeRequirements fn failures
        , suNeeds = needsOf fn failures
        , suRelations = relationsOf fn failures
        , suTrue = trueRanges fn stmts
        , suMadeSums = madeSums fn stmts
        , suMadeSizes = madeSizes fn stmts
        , suMadeStores = madeStores fn stmts
        , suLeaves = leavesOf fn cfg stmts
        , suGives = givenTo fn stmts
        , suGivesSums = givenSumsTo fn stmts
        , suOut = storedThrough fn stmts
        }

-- | What the analyses of functions say of them by name, on top of what was
-- known: a function defined more than once (for each platform) is what all
-- its definitions are. Requirements, relations and needs only grow: one
-- found stays assumed.
namedSummaries :: Env -> [Analysed] -> Env
namedSummaries env analysed = env
    { envReturns = Map.mapMaybe id $ Map.fromListWith (\a b -> min <$> a <*> b) (byName suSize)
    , envIntReturns = Map.filter (/= unknownRange) $ Map.mapMaybe id $ Map.fromListWith (\a b -> hull <$> a <*> b) (byName suRange)
    , envAtMost = Map.filter (not . Map.null) $ Map.fromListWith (Map.intersectionWith max) (byName suAtMost)
    , envAtMostUnless = Map.mapMaybe id $ Map.fromListWith bothUnless (byName suAtMostUnless)
    , envBelow = Map.mapMaybe id $ Map.fromListWith (\a b -> a <* guard (a == b)) (byName suBelow)
    , envAtMostPlaces = Map.filter (not . Map.null) $ Map.fromListWith (Map.intersectionWith max) (byName suAtMostPlaces)
    , envFailures = Map.mapMaybe id $ Map.fromListWith (\a b -> (\x y -> nub (x ++ y)) <$> a <*> b) (byName suFailures)
    , envRequires = Map.filter (not . Map.null) $ Map.unionWith (Map.unionWith intersectRange) (envRequires env)
        (Map.fromListWith (Map.unionWith intersectRange) (byName suRequires))
    -- A function defined more than once makes sure of what all its
    -- definitions do.
    , envPointsAtMost = Map.filter (not . Map.null) $ Map.unionWith (Map.unionWith min) (envPointsAtMost env)
        (Map.fromListWith (Map.unionWith min) (byName suPointsAtMost))
    , envTrue = Map.mapMaybe id $ Map.fromListWith (\a b -> Map.intersectionWith hull <$> a <*> b) (byName suTrue)
    , envMadeSums = Map.filter (not . null) $ Map.mapMaybe id $ Map.fromListWith (\a b -> bothSums <$> a <*> b) (byName suMadeSums)
    , envMadeStores = Map.filter (not . Map.null) $ Map.fromListWith (Map.intersectionWith hull) (byName suMadeStores)
    , envLeaves = Map.filter (not . Map.null) $ Map.fromListWith (Map.intersectionWith hull) (byName suLeaves)
    , envMadeSizes = Map.filter (not . Map.null) $ Map.fromListWith (\a b -> Map.mapMaybe id (Map.intersectionWith (\x y -> x <$ guard (x == y)) a b)) (byName suMadeSizes)
    , envRelations = Map.filter (not . null) $ Map.unionWith (\a b -> nub (a ++ b)) (envRelations env)
        (Map.fromListWith (++) (byName suRelations))
    , envNeeds = Map.filter (not . Map.null) $ Map.unionWith (Map.unionWith (\a b -> pruneNeeds (a ++ b))) (envNeeds env)
        (Map.fromListWith (Map.unionWith (\a b -> pruneNeeds (a ++ b))) (byName suNeeds))
    -- What every definition may store.
    , envStores = Map.filter (not . Map.null) $ Map.fromListWith (Map.intersectionWith (\(r1, m1) (r2, m2) -> (hull r1 r2, Map.intersectionWith max m1 m2)))
        (byName suOut)
    }
  where
    byName f = [ (fnName (anFunction a), f (anSummary a)) | a <- analysed ]
    bothSums a b = Map.toList (Map.intersectionWith min (Map.fromList a) (Map.fromList b))
    bothUnless a b = do
        (k, m) <- a
        (k', m') <- b
        guard (k == k')
        let both = Map.intersectionWith max m m'
        (k, both) <$ guard (not (Map.null both))

-- | The names whose summaries differ.
namedChanges :: Env -> Env -> Set.Set Text
namedChanges a b = Set.unions
    [ changedKeys (envReturns a) (envReturns b)
    , changedKeys (envIntReturns a) (envIntReturns b)
    , changedKeys (envAtMost a) (envAtMost b)
    , changedKeys (envAtMostUnless a) (envAtMostUnless b)
    , changedKeys (envBelow a) (envBelow b)
    , changedKeys (envAtMostPlaces a) (envAtMostPlaces b)
    , changedKeys (envMadeSizes a) (envMadeSizes b)
    , changedKeys (envMadeStores a) (envMadeStores b)
    , changedKeys (envLeaves a) (envLeaves b)
    , changedKeys (envFailures a) (envFailures b)
    , changedKeys (envRequires a) (envRequires b)
    , changedKeys (envPointsAtMost a) (envPointsAtMost b)
    , changedKeys (envRelations a) (envRelations b)
    , changedKeys (envTrue a) (envTrue b)
    , changedKeys (envMadeSums a) (envMadeSums b)
    , changedKeys (envNeeds a) (envNeeds b)
    , changedKeys (envStores a) (envStores b)
    ]

changedKeys :: (Ord k, Eq v) => Map k v -> Map k v -> Set.Set k
changedKeys a b = Set.filter (\k -> Map.lookup k a /= Map.lookup k b) (Map.keysSet a <> Map.keysSet b)

-- | Works out functions callees first, so that most are worked out with
-- what's known of what they call; each name's summaries are put in as soon
-- as its definitions so far are worked out. A function worked out before
-- something it uses was known (its own needs, or what it calls round a
-- cycle) is worked out again at the end. One worked out before, with what
-- it took from the summaries then, is kept if that's the same and nothing
-- else it uses has changed.
calleesFirst :: Env -> [(Function, Set.Set Text)] -> (Int -> Bool) -> Map Int (Analysed, [Named]) -> (Map Int (Analysed, [Named]), Env)
calleesFirst env0 functionsUsing changedFor before = (Map.mapWithKey again done, envDone)
  where
    functions = map fst functionsUsing
    uses = Map.fromList (zip [0 :: Int ..] (map snd functionsUsing))
    fnAt = Map.fromList (zip [0 :: Int ..] functions)
    again i (a, seen)
        | seen /= now = (analysedWith envDone (fnAt Map.! i), now)
        | otherwise = (a, seen)
      where
        now = inputs envDone i
    -- What a function's analysis takes from the summaries: those of what it
    -- names, but of its own only what it assumes of itself (unless it calls
    -- itself).
    inputs env i =
        let fn = fnAt Map.! i
            own = fnName fn
            recursive = or [ f == own | Fix (FunctionCall (Fix (VarExpr (L _ _ f))) _) <- subnodes (fnDefn fn) ]
            others = [ namedOf env n | n <- Set.toList (Map.findWithDefault Set.empty i uses), n /= own || recursive ]
        in assumedOf env own : others
    indexed = zip [0 :: Int ..] functions
    byName = Map.fromListWith (++) [ (fnName fn, [i]) | (i, fn) <- indexed ]
    -- Everything a function names that's a function, called or not.
    callees i = concat [ Map.findWithDefault [] f byName | f <- Set.toList (Map.findWithDefault Set.empty i uses), f /= fnName (fnAt Map.! i) ]
    order = Graph.flattenSCCs (Graph.stronglyConnComp [ ((i, fn), i, callees i) | (i, fn) <- indexed ])
    (done, envDone) = foldl' step (Map.empty, env0) order
    step (soFar, env) (i, fn) =
        let seen = inputs env i
            a = case Map.lookup i before of
                Just (b, seen') | not (changedFor i), seen' == seen -> b
                _ -> analysedWith env fn
            soFar' = Map.insert i (a, seen) soFar
            name = fnName fn
            defs = [ d | j <- Map.findWithDefault [] name byName, Just (d, _) <- [Map.lookup j soFar' <|> Map.lookup j before] ]
            named = namedSummaries env defs
            put field = Map.union (field named) (Map.delete name (field env))
        in ( soFar'
           , env { envReturns = put envReturns, envIntReturns = put envIntReturns, envAtMost = put envAtMost, envAtMostUnless = put envAtMostUnless, envBelow = put envBelow
                 , envFailures = put envFailures, envRequires = put envRequires, envPointsAtMost = put envPointsAtMost, envTrue = put envTrue
                 , envMadeSums = put envMadeSums, envAtMostPlaces = put envAtMostPlaces, envMadeSizes = put envMadeSizes, envMadeStores = put envMadeStores, envLeaves = put envLeaves
                 , envRelations = put envRelations, envNeeds = put envNeeds, envStores = put envStores }
           )

-- | Everything known of a name's summaries, to tell whether it changed.
data Named = Named
    (Maybe Integer) (Maybe Range) (Maybe (Map Int Integer)) (Maybe [Range]) (Maybe (Map Int Range))
    (Maybe [Lin]) (Maybe (Map Int Range)) (Maybe (Map Int [Lin])) (Maybe (Map Int (Range, Map Int Integer)))
    (Maybe [(Map ParamPlace Integer, Integer)]) (Maybe (Map ParamPlace Integer)) (Maybe (Map ParamPlace Lin))
    (Maybe (Integer, Map Int Integer)) (Maybe Int) (Maybe (Map Int Integer)) (Maybe (Map Int Range))
    (Maybe (Map ParamPlace Range))
    deriving (Eq)

-- | What a function assumes of itself where it starts.
assumedOf :: Env -> Text -> Named
assumedOf env name = Named Nothing Nothing Nothing Nothing (Map.lookup name (envRequires env))
    (Map.lookup name (envRelations env)) Nothing (Map.lookup name (envNeeds env)) Nothing Nothing Nothing Nothing Nothing Nothing
    (Map.lookup name (envPointsAtMost env)) Nothing Nothing

namedOf :: Env -> Text -> Named
namedOf env name = Named
    (get envReturns) (get envIntReturns) (get envAtMost) (get envFailures) (get envRequires)
    (get envRelations) (get envTrue) (get envNeeds) (get envStores) (get envMadeSums) (get envAtMostPlaces) (get envMadeSizes)
    (get envAtMostUnless) (get envBelow) (get envPointsAtMost) (get envMadeStores) (get envLeaves)
  where
    get :: (Env -> Map Text v) -> Maybe v
    get field = Map.lookup name (field env)

-- | Checks every call to a function with array parameters that have a size.
checkBufferSizes :: [(FilePath, [C.Node (Lexeme Text)])] -> [ErrorInfo p]
checkBufferSizes = sizeErrors . analyseBufferSizes

-- | Where the summary loop is with integer fields' ranges: hoping, checking
-- them each time round with what to fall back on, falling back on that, or
-- as they're known.
data FieldPhase
    = FirstRound
    | Checking (Map (Text, Text) Range)
    | FallingBack (Map (Text, Text) Range)
    | Safe

-- | Every function's analysis.
data Sizes = Sizes
    { szAnalysed  :: [Analysed]
    , szSummaries :: Summaries
    }

-- | Where each function may store, worked out once for every check.
sizeSummaries :: Sizes -> Summaries
sizeSummaries = szSummaries

sizeErrors :: Sizes -> [ErrorInfo p]
sizeErrors Sizes{szAnalysed = analysed} =
    [ failureError (fnFile fn) fl
    | Analysed{anFunction = fn, anCfg = cfg, anFacts = stmts} <- analysed
    , fl <- concat [ checkStmt (fnCtx fn) facts stmt | (facts, stmt) <- stmts ] ++ endFailures fn cfg
         ++ overflowsOnce (concat [ overflowFailures (fnCtx fn) facts stmt | (facts, stmt) <- stmts ])
    ]

-- | What's known in a statement: the least and the most an integer
-- variable or path is, where an expression starts (past what's checked
-- before it there: the left of @&&@, @||@ and @?:@), or else before the
-- statement; and the least elements a pointer expression in it has.
data Known = Known
    { knownLeast    :: Maybe C.AlexPosn -> Text -> Maybe Integer
    , knownMost     :: Maybe C.AlexPosn -> Text -> Maybe Integer
    , knownElements :: C.Node (Lexeme Text) -> Maybe Integer
    }

-- | What's known in each statement of each function: by the function's
-- file and where its name is, then the statement's block and place in it.
leastBefore :: Sizes -> Map (FilePath, C.AlexPosn) (Map (Int, Int) Known)
leastBefore Sizes{szAnalysed = analysed} = Map.fromList
    [ ((fnFile fn, pos), Map.fromList (zip keys [ knownIn (fnCtx fn) facts stmt | (facts, stmt) <- stmts ]))
    | Analysed{anFunction = fn, anCfg = cfg, anFacts = stmts} <- analysed
    , Just (L pos _ _) <- [fcLoc (fnCtx fn)]
    , let keys = [ (cfgNodeId n, i) | n <- Map.elems cfg, i <- [0 .. length (cfgStmts n) - 1] ]
    ]
  where
    knownIn ctx facts stmt =
        let evaluated = evaluatedWithFacts ctx facts stmt
            at = Map.fromListWith both
                [ (p, least ctx fs) | (fs, _, e) <- evaluated, Just (L p _ _) <- [getLexeme e] ]
            atMost = Map.fromListWith (\f g v -> max <$> f v <*> g v)
                [ (p, most ctx fs) | (fs, _, e) <- evaluated, Just (L p _ _) <- [getLexeme e] ]
            factsAt e = fromMaybe facts (listToMaybe [ fs | (fs, _, e') <- evaluated, e' == e ])
        in Known
            { knownLeast = \pos -> fromMaybe (least ctx facts) (pos >>= (`Map.lookup` at))
            , knownMost = \pos -> fromMaybe (most ctx facts) (pos >>= (`Map.lookup` atMost))
            , knownElements = \e -> let fs = factsAt e in sizeOf ctx fs e >>= lowerBound fs
            }
    -- Expressions from one place in a macro, where it's used more than once.
    both f g v = min <$> f v <*> g v
    least _ Unreached _ = Nothing
    least ctx facts v0 =
        let v = placeNamed ctx v0
        in case catMaybes [rLow (placeRange ctx v facts), lowerLin facts (linVar v)] of
            [] -> Nothing
            ks -> Just (maximum ks)
    most _ Unreached _ = Nothing
    most ctx facts v0 =
        let v = placeNamed ctx v0
        in case catMaybes [rHigh (placeRange ctx v facts), upperLin facts (linVar v)] of
            [] -> Nothing
            ks -> Just (minimum ks)

analyseBufferSizes :: [(FilePath, [C.Node (Lexeme Text)])] -> Sizes
analyseBufferSizes parsed =
    let files = scopeMacros parsed
        env0 = withKeeps (collectEnv (concatMap snd files))
        withKeeps e = e { envKeeps = keptParams e (concatMap snd files), envReturnsPlace = returnedPlaces (concatMap snd files) }
        initialised = [ (key, Nothing) | node <- concatMap snd files, key <- initialisedFields env0 node ]
        asValues = foldMap (foldMap usedAsValues . snd) files
        called = Set.fromList [ f | (_, nodes) <- files, node <- nodes, Fix (FunctionCall (Fix (VarExpr (L _ _ f))) _) <- subnodes node ]
        storeSummaries = summarise env0 (concatMap snd files)
        functions0 = concat [ concatMap (functionsOf env0 storeSummaries asValues called file) nodes | (file, nodes) <- files ]
        -- All a function's analysis takes from the summaries is under the
        -- names in it (what it calls, its own) and the fields it uses.
        mentions =
            [ (Set.fromList ([ t | L _ _ t <- foldFix C.lexemes (fnDefn fn) ] ++ calledThrough fn), fieldsUsed fn)
            | fn <- functions0 ]
        -- The functions a call through a pointer may be to.
        calledThrough fn =
            [ g
            | Fix (FunctionCall f _) <- subnodes (fnDefn fn)
            , case f of
                Fix VarExpr{} -> False
                _             -> True
            , Just t <- [exprType (fnCtx fn) f]
            , g <- targetsOf storeSummaries (ctName (resolveType env0 t))
            ]
        fieldsUsed fn = Set.fromList
            [ k
            | e@(Fix node) <- subnodes (fnDefn fn)
            , case node of
                PointerAccess{} -> True
                MemberAccess{}  -> True
                _               -> False
            , Just k <- [fieldKey (fnCtx fn) e]
            ]
        -- A static function never used as a value, defined only so, is
        -- given only what the program's calls to it give it, if they can all
        -- be seen.
        closed = Set.fromList [ fnName fn | fn <- functions0, fnClosed fn ]
            `Set.difference` Set.fromList [ fnName fn | fn <- functions0, not (fnClosed fn) ]
            `Set.difference` foldMap (foldMap calledUnseen . snd) files
        (first, known) = calleesFirst env0 { envClosed = closed } (zip functions0 (map fst mentions)) (const True) Map.empty
        closed' = closed `Set.difference` foldMap (calledOffGraph . fst) first
        -- Unions, structs given something but zeros where they're made,
        -- those given bytes, and the structs in them: any of their fields
        -- may be anything.
        withBytes = inStructs (Set.fromList (concatMap (concatMap (initialisedWith env0) . snd) files) <> rawStructs storeSummaries)
        inStructs set =
            let set' = set <> Set.fromList
                    [ ctName u
                    | st <- Set.toList set
                    , ft <- maybe [] Map.elems (Map.lookup st (envStructs env0))
                    , let u = resolveType env0 ft
                    , ctPointers u == 0
                    , Map.member (ctName u) (envStructs env0) ]
            in if set' == set then set else inStructs set'
        analysed = summaries initialised withBytes functions0 mentions FirstRound known { envClosed = closed' } (10 :: Int) first
    in Sizes analysed storeSummaries
  where
    -- What functions return, fields hold and static functions need depends
    -- on the same of other functions: go round until nothing changes,
    -- working out again only the functions that use a summary that did. A
    -- field that is ever given something of unknown size has none.
    summaries initialised withBytes functions0 mentions phase env n done
        | not changed = analysed
        | n <= 1, Checking safe <- phase = summaries initialised withBytes functions0 mentions (FallingBack safe) env' 10 done'
        | n <= 1 = analysed'
        | otherwise = summaries initialised withBytes functions0 mentions phase' env' (n - 1) done'
      where
        analysed = map fst (Map.elems done)
        named = namedSummaries env analysed
        fields = Map.mapMaybe id $ Map.fromListWith (\a b -> min <$> a <*> b)
            (initialised ++ concatMap (suStores . anSummary) analysed)
        -- An integer field is what it's given, or zero, as structs start,
        -- but for the structs given bytes. The first time round, it's hoped
        -- to be what it's given if counts taken down don't wrap round. Once
        -- all else stays the same, a field given more than hoped is given up
        -- on, so that where nothing changes, what's left holds. What it's
        -- known to be from the first time round alone is what's left if
        -- that doesn't come.
        ranges pick = Map.filterWithKey (\(st, _) _ -> Set.notMember st withBytes) $
            Map.fromListWith hull [ (k, hull (exactly 0) (pick (r, h))) | a <- analysed, (k, r, h) <- suFields (anSummary a) ]
        (fieldRanges', phase') = case phase of
            FirstRound -> (ranges snd, Checking (ranges fst))
            Checking safe
                | Set.null changedNames && Set.null changedGiven && envFields env == fields ->
                    let given' = ranges fst
                    in (Map.filterWithKey (\k r -> maybe True (`within` r) (Map.lookup k given')) (envFieldRanges env), Checking safe)
                | otherwise -> (envFieldRanges env, Checking safe)
            FallingBack safe -> (safe, Safe)
            Safe -> (envFieldRanges env, Safe)
        -- What every call gives, worked out again each time round from
        -- what was known before, which held.
        given = Map.filter (not . Map.null) $ Map.map (Map.filter (/= unknownRange)) $ (`Map.restrictKeys` envClosed env)
            (Map.unionsWith (Map.unionWith hull) (map (suGives . anSummary) analysed))
        givenSums = Map.map Map.toList $ Map.filter (not . Map.null) $ (`Map.restrictKeys` envClosed env)
            (Map.unionsWith (Map.intersectionWith min) (map (suGivesSums . anSummary) analysed))
        env' = named { envFields = fields, envFieldRanges = fieldRanges', envGiven = given, envGivenSums = givenSums }
        changedNames = namedChanges env named
        -- Only a function itself takes what its calls give it.
        changedGiven = changedKeys (envGiven env) given <> changedKeys (envGivenSums env) givenSums
        changedFields = changedKeys (envFields env) fields <> changedKeys (envFieldRanges env) fieldRanges'
        changed = not (Set.null changedNames && Set.null changedGiven && Set.null changedFields)
        -- Worked out again callees first: what a function takes from the
        -- summaries is compared there, so only what else it uses is here.
        changedFor = (Map.fromList (zip [0 ..] (zipWith changedIn functions0 mentions)) Map.!)
        changedIn fn0 (_, used) = Set.member (fnName fn0) changedGiven || not (Set.disjoint changedFields used)
        done' = fst (calleesFirst env' (zip functions0 (map fst mentions)) changedFor done)
        analysed' = map fst (Map.elems done')
