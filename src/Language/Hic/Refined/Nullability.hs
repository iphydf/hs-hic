{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StrictData            #-}

-- | Null pointers, followed through each function: one that may be null
-- must not be dereferenced, called, or given where it's declared @_Nonnull@
-- (a parameter, a field, a variable, or what a function returns).
--
-- What may be null comes from declarations: a pointer declared @_Nullable@,
-- or with neither, may be. Checks (@p == nullptr@, @!p@, @p && ...@, an
-- assert) tell where it isn't, and where it is. After a pointer is
-- dereferenced or given where it must not be null, it isn't: where it may
-- have been is reported there.
--
-- A buffer with a length (a parameter followed by its length, a field with
-- its length field, an array with its count) has as many elements as the
-- length says, which is checked wherever it's given or seen ("BufferSize"),
-- and one that's null has none: where the length is known to be at least 1,
-- the buffer isn't null.
module Language.Hic.Refined.Nullability
    ( checkNullability
    ) where

import           Control.Monad                         (guard)
import           Control.Monad.Identity                (Identity (..))
import           Data.Containers.ListUtils             (nubOrd)
import           Data.Fix                              (Fix (..))
import           Data.Foldable                         (toList)
import           Data.List                             (foldl', mapAccumL)
import qualified Data.Map.Merge.Strict                 as Merge
import           Data.Map.Strict                       (Map)
import qualified Data.Map.Strict                       as Map
import           Data.Maybe                            (catMaybes, fromMaybe,
                                                        isJust)
import qualified Data.Set                              as Set
import           Data.Text                             (Text)
import qualified Data.Text                             as T
import           Language.Cimple                       (Lexeme (..), NodeF (..))
import qualified Language.Cimple                       as C
import           Language.Cimple.Pretty                (showNodePlain)
import           Language.Hic.Core.AstUtils            (getLexeme)
import           Language.Hic.Core.DataFlow            (CFG, CFGNode (..),
                                                        DataFlow (..), buildCFG,
                                                        fixpoint)
import           Language.Hic.Core.Errors              (Context (..),
                                                        ErrorInfo (..),
                                                        NullUse (..),
                                                        TypeError (..))
import           Language.Hic.Refined.BufferSize       (Known (..), Sizes,
                                                        leastBefore,
                                                        sizeSummaries)
import           Language.Hic.Refined.BufferSize.Env   (CType (..), Env (..),
                                                        FieldPair (..),
                                                        Param (..),
                                                        Signature (..),
                                                        collectEnv, declType,
                                                        isNullptr,
                                                        isPointerType, localsOf,
                                                        resolveType, subnodes,
                                                        typeOfExpr)
import           Language.Hic.Refined.BufferSize.Paths
import           Language.Hic.Refined.Effects          (Effects (..), Loc (..),
                                                        Summaries, callEffects,
                                                        expandIn, footprint,
                                                        mayChange, scopeMacros,
                                                        storeAt)
import           Text.Read                             (readMaybe)

------------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------------

-- | What one level of a pointer is declared to be.
data Declared = DeclNonnull | DeclNullable | DeclUnspecified
    deriving (Show, Eq)

-- | The levels of a declaration's pointers, outermost first. An array is a
-- level that is never null, but for an array parameter, which is a pointer.
type Shape = [Declared]

data Contract = Contract
    { coParams :: [Maybe Shape]
      -- ^ One per parameter; 'Nothing' for @...@.
    , coReturn :: Shape
    }

-- | What the program declares of pointers.
data Decls = Decls
    { dFunctions :: Map Text Contract
      -- ^ Functions, and function typedefs for calls through pointers.
    , dFields    :: Map (Text, Text) Shape
      -- ^ By struct (or union) and field.
    , dGlobals   :: Map Text Shape
    , dBeside    :: Map (Text, Text) [Text]
      -- ^ Fields only stored with others on the same object, which aren't
      -- null where the first isn't: a callback and the object it's given.
    , dOutSets   :: Map Text OutSets
      -- ^ Functions returning only numbers, and what they store through
      -- their out-parameters as they return each.
    }

-- | Where a function returns: what it may return there, and the
-- out-parameters (pointers to pointers) it has stored a pointer that isn't
-- null through by then.
newtype OutSets = OutSets { osReturns :: [(Interval, Set.Set Int)] }

-- | The least and the most a number may be, if known.
type Interval = (Maybe Integer, Maybe Integer)

overlaps :: Interval -> Interval -> Bool
overlaps (lo1, hi1) (lo2, hi2) = case (maxBound' lo1 lo2, minBound' hi1 hi2) of
    (Just lo, Just hi) -> lo <= hi
    _                  -> True
  where
    maxBound' a b = maybe b (\x -> Just (maybe x (max x) b)) a
    minBound' a b = maybe b (\x -> Just (maybe x (min x) b)) a

-- | The numbers a comparison with a number says something is in, where
-- it's true or false.
comparedWith :: C.BinaryOp -> Integer -> Bool -> [Interval]
comparedWith op k truth = case (op, truth) of
    (C.BopEq, True)  -> [(Just k, Just k)]
    (C.BopEq, False) -> [(Nothing, Just (k - 1)), (Just (k + 1), Nothing)]
    (C.BopNe, t)     -> comparedWith C.BopEq k (not t)
    (C.BopLt, True)  -> [(Nothing, Just (k - 1))]
    (C.BopLt, False) -> [(Just k, Nothing)]
    (C.BopLe, True)  -> [(Nothing, Just k)]
    (C.BopLe, False) -> [(Just (k + 1), Nothing)]
    (C.BopGt, True)  -> [(Just (k + 1), Nothing)]
    (C.BopGt, False) -> [(Nothing, Just k)]
    (C.BopGe, True)  -> [(Just k, Nothing)]
    (C.BopGe, False) -> [(Nothing, Just (k - 1))]
    _                -> [(Nothing, Nothing)]

-- | The out-parameters every return a call may have made, of those in
-- some of the intervals, stored through.
storedWhere :: OutSets -> [Interval] -> Set.Set Int
storedWhere os ivs = case [ st | (iv, st) <- osReturns os, any (overlaps iv) ivs ] of
    []       -> Set.empty
    st : sts -> foldl' Set.intersection st sts

typeShape :: C.Node (Lexeme Text) -> Shape
typeShape = go DeclUnspecified
  where
    go q (Fix t) = case t of
        TyNonnull x                            -> go DeclNonnull x
        TyNullable x                           -> go DeclNullable x
        TyConst x                              -> go q x
        TyOwner x                              -> go q x
        TyForce x                              -> go q x
        TyBitwise x                            -> go q x
        TyPointer x                            -> q : go DeclUnspecified x
        -- Only a pointer (or an array parameter) can say whether it's
        -- null, so a typedef that does is one.
        TyUserDefined{} | q /= DeclUnspecified -> [q]
        _                                      -> []

-- | A declaration's shape: its array dimensions, then its type's pointers.
-- A parameter's first dimension is a pointer, declared as it says.
declShape :: Bool -> C.Node (Lexeme Text) -> [C.Node (Lexeme Text)] -> Shape
declShape isParam ty dims = zipWith dim [0 :: Int ..] dims ++ typeShape ty
  where
    dim i (Fix (DeclSpecArray n _)) | isParam && i == 0 = case n of
        C.Nonnull                -> DeclNonnull
        C.Nullable               -> DeclNullable
        C.NullabilityUnspecified -> DeclUnspecified
    dim _ _ = DeclNonnull

paramShape :: C.Node (Lexeme Text) -> Maybe Shape
paramShape (Fix p) = case p of
    VarDecl ty _ dims -> Just (declShape True ty dims)
    NonNullParam d    -> withTop DeclNonnull <$> paramShape d
    NullableParam d   -> withTop DeclNullable <$> paramShape d
    Commented _ d     -> paramShape d
    _                 -> Nothing
  where
    withTop q = \case
        _ : rest -> q : rest
        []       -> []

-- | Of two declarations of the same thing, at each level what either says.
mergeShape :: Shape -> Shape -> Shape
mergeShape a b = zipWith pick a b ++ drop (length b) a ++ drop (length a) b
  where
    pick DeclUnspecified y = y
    pick x _               = x

declsOf :: [C.Node (Lexeme Text)] -> Decls
declsOf nodes = Decls
    { dFunctions = Map.unionWith merge contracts (Map.fromListWith merge declaredAs)
    , dFields = Map.fromList (concatMap fields nodes)
    , dGlobals = Map.fromList (concatMap globals nodes)
    , dBeside = Map.empty
    , dOutSets = Map.empty
    }
  where
    merge (Contract p1 r1) (Contract p2 r2) =
        Contract (zipWith (\a b -> mergeShape <$> a <*> b) p1 p2) (mergeShape r1 r2)
    contracts = Map.fromListWith merge (concatMap prototypes nodes)
    -- A function declared with a function type (@static obj_cb handler;@)
    -- has that type's contract.
    declaredAs =
        [ (name, c)
        | Fix (CallbackDecl (L _ _ t) (L _ _ name)) <- concatMap subnodes nodes
        , Just c <- [Map.lookup t contracts]
        ]
    prototypes (Fix node) = case node of
        FunctionPrototype ret (L _ _ name) params ->
            [(name, Contract (map paramShape (filter isParam params)) (typeShape ret))]
        _ -> concatMap prototypes (toList node)
    isParam (Fix p) = case p of
        TyStd{} -> False
        _       -> True
    fields (Fix node) = case node of
        Struct (L _ _ s) members -> [ ((s, f), shape) | (f, shape) <- concatMap member members ] ++ concatMap fields members
        Union (L _ _ s) members  -> [ ((s, f), shape) | (f, shape) <- concatMap member members ] ++ concatMap fields members
        FunctionDefn{}           -> []
        _                        -> concatMap fields (toList node)
    member (Fix m) = case m of
        MemberDecl (Fix (VarDecl ty (L _ _ f) dims)) _ -> [(f, declShape False ty dims)]
        Commented _ d                                  -> member d
        _                                              -> []
    globals (Fix node) = case node of
        VarDeclStmt (Fix (VarDecl ty (L _ _ name) dims)) _ -> [(name, declShape False ty dims)]
        ConstDefn _ ty (L _ _ name) _                     -> [(name, typeShape ty)]
        FunctionDefn{}                                    -> []
        Struct{}                                          -> []
        Union{}                                           -> []
        _                                                 -> concatMap globals (toList node)

------------------------------------------------------------------------------
-- Facts
------------------------------------------------------------------------------

data Null = NotNull | MaybeNull | IsNull
    deriving (Show, Eq)

joinNull :: Null -> Null -> Null
joinNull a b = if a == b then a else MaybeNull

declaredNull :: Shape -> Null
declaredNull = \case
    DeclNonnull : _ -> NotNull
    _               -> MaybeNull

-- | What's known of a place, against what its declaration says, which is
-- what's known of it where nothing else is.
data Entry = Entry
    { enNow      :: Null
    , enDeclared :: Null
    , enPath     :: Path
    , enFoot     :: [Loc]
      -- ^ What a store may change it through ('footprint').
    }
    deriving (Show, Eq)

data Facts
    = Unreached
    | Facts (Map Text Entry)
      -- ^ By the place as written: only those known to be other than
      -- declared.
    deriving (Show, Eq)

joinFacts :: Facts -> Facts -> Facts
joinFacts Unreached b = b
joinFacts a Unreached = a
joinFacts (Facts a) (Facts b) = Facts $ Merge.merge
    (Merge.mapMaybeMissing (const widened))
    (Merge.mapMaybeMissing (const widened))
    (Merge.zipWithMaybeMatched (\_ x y -> kept x { enNow = joinNull (enNow x) (enNow y) }))
    a b
  where
    widened x = kept x { enNow = joinNull (enNow x) (enDeclared x) }

kept :: Entry -> Maybe Entry
kept en = if enNow en == enDeclared en then Nothing else Just en

setEntry :: Entry -> Facts -> Facts
setEntry _ Unreached       = Unreached
setEntry en (Facts facts) = Facts (Map.alter (const (kept en)) (pathName (enPath en)) facts)

------------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------------

-- | What one function's analysis needs.
data Ctx l = Ctx
    { cxEnv       :: Env
    , cxDecls     :: Decls
    , cxTypes     :: Map Text CType
      -- ^ Parameters, locals and globals.
    , cxShapes    :: Map Text Shape
      -- ^ The same.
    , cxEscaped   :: Set.Set Text
      -- ^ Variables a call or a store through a pointer may change: globals,
      -- and those whose address is taken.
    , cxName      :: Text
    , cxReturn    :: Shape
    , cxLengths   :: Map Text Text
      -- ^ Parameters followed by their lengths, if the function changes
      -- neither.
    , cxStored    :: Set.Set Text
      -- ^ Fields the function may have stored to, before the statement
      -- checked or in it.
    , cxLeast     :: Maybe C.AlexPosn -> Text -> Maybe Integer
      -- ^ The least an integer variable or path is known to be in the
      -- statement checked, where an expression starts.
    , cxMost      :: Maybe C.AlexPosn -> Text -> Maybe Integer
      -- ^ The most, the same way.
    , cxElements  :: C.Node (Lexeme Text) -> Maybe Integer
      -- ^ The least elements a pointer in the statement checked is known
      -- to have there.
    , cxSummaries :: Summaries
      -- ^ Where each function may store.
    , cxBound     :: Map Text (C.Node (Lexeme Text))
      -- ^ Variables never stored to after they're declared with a call: the
      -- call.
    , cxOutVars   :: Set.Set Text
      -- ^ Pointers never stored to but by the one call given their address.
    , cxOutCalls  :: Map Text (Text, Int, Text)
      -- ^ Of those, the ones whose call is what a variable is declared
      -- with: the function, which argument it is, and the variable.
    }

instance DataFlow Identity Ctx Text Facts () where
    emptyFacts _ = return Unreached
    join _ a b = return (joinFacts a b)
    transfer ctx _ _ facts stmt = return (fst (stepStmt ctx facts stmt), Set.empty)

functionsIn :: Env -> Decls -> Summaries -> C.Node (Lexeme Text) -> [(Ctx Text, C.AlexPosn, C.Node (Lexeme Text))]
functionsIn env decls summaries n@(Fix node) = case node of
    FunctionDefn _ (Fix (FunctionPrototype ret (L loc _ name) params)) body ->
        let own = [ (pname, ty, fromMaybe [] (paramShape p))
                  | p <- filter isDecl params
                  , Just (pname, ty) <- [declType env p]
                  ] `withDeclared` Map.lookup name (dFunctions decls)
            ownTypes = Map.fromList [ (p, ty) | (p, ty, _) <- own ]
            localTypes = Map.fromList (localsOf env (ownTypes <> envGlobals env) body)
            localShapes = addressArrays body `Map.union` Map.fromList (concat
                [ case local of
                    VarDecl ty (L _ _ v) dims -> [(v, declShape False ty dims)]
                    VLA _ (L _ _ v) _         -> [(v, [DeclNonnull])]
                    _                         -> []
                | Fix local <- subnodes body ])
            types = Map.unions [localTypes, ownTypes, envGlobals env]
            shapes = Map.unions [localShapes, Map.fromList [ (p, s) | (p, _, s) <- own ], dGlobals decls]
            ownNames = Map.keysSet localTypes <> Map.keysSet ownTypes
            escaped = (Map.keysSet (envGlobals env) `Set.difference` ownNames) <> addressTaken body
            ret' = maybe (typeShape ret) (mergeShape (typeShape ret) . coReturn) (Map.lookup name (dFunctions decls))
            (assigned, stored) = changedIn body
            names = [ p | (p, _, _) <- own ]
            lengths = Map.fromList
                [ (p, len)
                | Just sig <- [Map.lookup name (envFunctions env)]
                , (p, Just param) <- zip names (sigParams sig)
                , Just k <- [paramLength param]
                , Just len <- [lookup k (zip [0 ..] names)]
                , not (any (`Set.member` (assigned <> escaped)) [p, len])
                ]
            assignedTo = [ v | Fix (AssignExpr (Fix (VarExpr (L _ _ v))) _ _) <- subnodes body ]
                ++ [ v | Fix (UnaryExpr o (Fix (VarExpr (L _ _ v)))) <- subnodes body, o `elem` [C.UopIncr, C.UopDecr] ]
            bound = Map.fromList
                [ (v, call)
                | Fix (VarDeclStmt (Fix (VarDecl _ (L _ _ v) [])) (Just call@(Fix FunctionCall{}))) <- subnodes body
                , v `notElem` assignedTo ]
            addressed = Map.fromListWith (+) [ (v, 1 :: Int) | Fix (UnaryExpr C.UopAddress (Fix (VarExpr (L _ _ v)))) <- subnodes body ]
            givenToCalls = Map.fromListWith (+) [ (v, 1 :: Int) | Fix (FunctionCall _ args) <- subnodes body, Fix (UnaryExpr C.UopAddress (Fix (VarExpr (L _ _ v)))) <- args ]
            outVars = Set.fromList [ v | (v, 1) <- Map.toList addressed, Map.lookup v givenToCalls == Just 1, v `notElem` assignedTo ]
            outCalls = Map.fromList
                [ (x, (f, k, v))
                | (v, Fix (FunctionCall (Fix (VarExpr (L _ _ f))) args)) <- Map.toList bound
                , (k, Fix (UnaryExpr C.UopAddress (Fix (VarExpr (L _ _ x))))) <- zip [0 ..] args
                , Set.member x outVars ]
        in [(Ctx env decls types shapes escaped name ret' lengths stored (\_ _ -> Nothing) (\_ _ -> Nothing) (const Nothing) summaries bound outVars outCalls, loc, n)]
    FunctionDefn{} -> []
    _ -> concatMap (functionsIn env decls summaries) (toList node)
  where
    isDecl (Fix p) = case p of
        TyStd{} -> False
        _       -> True
    -- The prototype may say more than the definition does.
    withDeclared ps = \case
        Just c  -> [ (p, ty, maybe s (mergeShape s) d) | ((p, ty, s), d) <- zip ps (coParams c ++ repeat Nothing) ]
        Nothing -> ps

-- | Local arrays of pointers that can't change, given only addresses: their
-- elements aren't null.
addressArrays :: C.Node (Lexeme Text) -> Map Text Shape
addressArrays body = Map.fromList
    [ (v, map (const DeclNonnull) dims ++ [DeclNonnull] ++ drop 1 (typeShape ty))
    | Fix (VarDeclStmt (Fix (VarDecl ty@(Fix (TyConst (Fix TyPointer{}))) (L _ _ v) dims@[_])) (Just (Fix (InitialiserList es)))) <- subnodes body
    , not (null es)
    , all isAddress es
    ]
  where
    isAddress (Fix e) = case e of
        UnaryExpr C.UopAddress _ -> True
        ParenExpr x              -> isAddress x
        _                        -> False

-- | Variables the function assigns to, and fields it may store to: those
-- it assigns to, or takes the address of.
changedIn :: C.Node (Lexeme Text) -> (Set.Set Text, Set.Set Text)
changedIn body = (Set.fromList [ pathRoot p | p <- targets, null (pathSteps p) ], Set.fromList [ f | p <- targets, Field f : _ <- [reverse (pathSteps p)] ])
  where
    targets = concat
        [ case node of
            AssignExpr lhs _ _ -> maybe [] pure (pathOf lhs)
            UnaryExpr o x | o `elem` [C.UopIncr, C.UopDecr, C.UopAddress] -> maybe [] pure (pathOf x)
            _ -> []
        | Fix node <- subnodes body ]

-- | Variables whose address is taken: of them, or of their fields
-- (@&v.f@, but not @&v->f@).
addressTaken :: C.Node (Lexeme Text) -> Set.Set Text
addressTaken body = Set.fromList
    [ pathRoot p
    | Fix (UnaryExpr C.UopAddress x) <- subnodes body
    , Just p <- [pathOf x]
    , all isField (pathSteps p)
    ]
  where
    isField = \case
        Field _ -> True
        _       -> False

------------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------------

exprType :: Ctx Text -> C.Node (Lexeme Text) -> Maybe CType
exprType ctx = typeOfExpr (cxEnv ctx) (cxTypes ctx)

isVariable :: Ctx Text -> Text -> Bool
isVariable ctx v = Map.member v (cxTypes ctx) || Map.member v (cxShapes ctx)

-- | What a call's callee is declared to take and give.
contractOf :: Ctx Text -> C.Node (Lexeme Text) -> Maybe Contract
contractOf ctx f = case f of
    Fix (VarExpr (L _ _ name)) | not (isVariable ctx name) -> Map.lookup name (dFunctions (cxDecls ctx))
    _ -> exprType ctx f >>= \t -> Map.lookup (ctName t) (dFunctions (cxDecls ctx))

-- | What an expression's declarations say of its pointers.
shapeOf :: Ctx Text -> C.Node (Lexeme Text) -> Shape
shapeOf ctx e@(Fix node) = case node of
    VarExpr (L _ _ v)
        | Just s <- Map.lookup v (cxShapes ctx) -> s
        -- Not a variable: a function, the library's if not the program's.
        | not (isVariable ctx v) -> [DeclNonnull]
        | otherwise -> []
    ParenExpr x -> shapeOf ctx x
    CastExpr _ x -> shapeOf ctx x
    PointerAccess b (L _ _ f) -> field b f
    MemberAccess b (L _ _ f) -> field b f
    UnaryExpr C.UopDeref x -> drop 1 (shapeOf ctx x)
    ArrayAccess x _ -> drop 1 (shapeOf ctx x)
    UnaryExpr C.UopAddress x -> DeclNonnull : shapeOf ctx x
    FunctionCall f _ -> maybe [] coReturn (contractOf ctx f)
    LiteralExpr C.String _ -> [DeclNonnull]
    BinaryExpr a op b | op `elem` [C.BopPlus, C.BopMinus] ->
        if isPointer ctx a then shapeOf ctx a else shapeOf ctx b
    _ | isPointer ctx e -> [DeclUnspecified]
    _ -> []
  where
    field b f = fromMaybe [] $ do
        st <- structOf ctx b
        Map.lookup (st, f) (dFields (cxDecls ctx))

-- | The struct (or union) a field access's object is, through a pointer
-- or not.
structOf :: Ctx Text -> C.Node (Lexeme Text) -> Maybe Text
structOf ctx b = ctName . resolveType (cxEnv ctx) <$> exprType ctx b

isPointer :: Ctx Text -> C.Node (Lexeme Text) -> Bool
isPointer ctx = maybe False isPointerType . exprType ctx

-- | Whether a pointer may be null, where facts are known.
valueOf :: Ctx Text -> Map Text Entry -> C.Node (Lexeme Text) -> Null
valueOf ctx facts e@(Fix node)
    | isNullptr e = IsNull
    | isNamedByC e = NotNull
    | Just p <- pathOf e, Just en <- Map.lookup (pathName p) facts = enNow en
    | otherwise = case node of
        ParenExpr x -> valueOf ctx facts x
        CastExpr _ x -> valueOf ctx facts x
        BinaryExpr a op b | op `elem` [C.BopPlus, C.BopMinus] ->
            valueOf ctx facts (if isPointer ctx a then a else b)
        TernaryExpr c a b -> case (narrow ctx True c (Facts facts), narrow ctx False c (Facts facts)) of
            (Unreached, Facts f) -> valueOf ctx f b
            (Facts f, Unreached) -> valueOf ctx f a
            (Facts f, Facts g)   -> joinNull (valueOf ctx f a) (valueOf ctx g b)
            _                    -> NotNull
        _ -> declaredNull (shapeOf ctx e)

-- | What C names for the file and function it's in: a string, and an
-- array.
isNamedByC :: C.Node (Lexeme Text) -> Bool
isNamedByC (Fix node) = case node of
    VarExpr (L _ _ v)       -> v `elem` ["__FILE__", "__func__"]
    LiteralExpr _ (L _ _ v) -> v `elem` ["__FILE__", "__func__"]
    _                       -> False

-- | Where a check of an expression says something about: through
-- parentheses and casts.
checkedPlace :: C.Node (Lexeme Text) -> C.Node (Lexeme Text)
checkedPlace e@(Fix node) = case node of
    ParenExpr x  -> checkedPlace x
    CastExpr _ x -> checkedPlace x
    _            -> e

-- | What's known after a pointer is found to be null or not. If that can't
-- be, it isn't reached.
setNull :: Ctx Text -> C.Node (Lexeme Text) -> Null -> Facts -> Facts
setNull ctx e0 s facts = foldl' (\acc o -> setOne ctx o NotNull acc) (setOne ctx e s facts) beside
  where
    e = checkedPlace e0
    -- Once a field isn't null, nor are those stored with it.
    beside
        | s /= NotNull = []
        | otherwise = case unFix e of
            PointerAccess b (L p c f) -> [ Fix (PointerAccess b (L p c o)) | o <- besideOf b f ]
            MemberAccess b (L p c f)  -> [ Fix (MemberAccess b (L p c o)) | o <- besideOf b f ]
            _                         -> []
    besideOf b f = maybe [] (\st -> Map.findWithDefault [] (st, f) (dBeside (cxDecls ctx))) (structOf ctx b)

-- | What's known after one pointer is found to be null or not.
setOne :: Ctx Text -> C.Node (Lexeme Text) -> Null -> Facts -> Facts
setOne _ _ _ Unreached = Unreached
setOne ctx e s fs@(Facts facts)
    | contradicts (valueOf ctx facts e) = Unreached
    | Just p <- pathOf e = setEntry (Entry s (declaredNull (shapeOf ctx e)) p (footOf ctx e)) fs
    | otherwise = fs
  where
    contradicts now = (now == NotNull && s == IsNull) || (now == IsNull && s == NotNull)

-- | What's known where a condition is true, or false.
narrow :: Ctx Text -> Bool -> C.Node (Lexeme Text) -> Facts -> Facts
narrow _ _ _ Unreached = Unreached
narrow ctx truth c@(Fix node) facts = case node of
    ParenExpr x -> narrow ctx truth x facts
    UnaryExpr C.UopNot x -> narrow ctx (not truth) x facts
    BinaryExpr a C.BopEq b
        | isNullptr b -> isNull truth a
        | isNullptr a -> isNull truth b
    BinaryExpr a C.BopNe b
        | isNullptr b -> isNull (not truth) a
        | isNullptr a -> isNull (not truth) b
    BinaryExpr a C.BopAnd b
        | truth -> narrow ctx True b (narrow ctx True a facts)
        | otherwise -> joinFacts (narrow ctx False a facts) (narrow ctx False b (narrow ctx True a facts))
    BinaryExpr a C.BopOr b
        | truth -> joinFacts (narrow ctx True a facts) (narrow ctx True b (narrow ctx False a facts))
        | otherwise -> narrow ctx False b (narrow ctx False a facts)
    BinaryExpr a op b
        | Just k <- constOf b, Just call <- resultOf a, op `elem` comparisons -> outsWhere call (comparedWith op k truth)
        | Just k <- constOf a, Just call <- resultOf b, Just op' <- lookup op flipped -> outsWhere call (comparedWith op' k truth)
    _ | isPointer ctx c -> isNull (not truth) c
    _ | Just call <- resultOf c -> outsWhere call (comparedWith C.BopNe 0 truth)
    _ -> facts
  where
    isNull yes x = setNull ctx x (if yes then IsNull else NotNull) facts
    comparisons = [C.BopEq, C.BopNe, C.BopLt, C.BopLe, C.BopGt, C.BopGe]
    -- k < r is r > k.
    flipped = [(C.BopEq, C.BopEq), (C.BopNe, C.BopNe), (C.BopLt, C.BopGt), (C.BopLe, C.BopGe), (C.BopGt, C.BopLt), (C.BopGe, C.BopLe)]
    -- A call (or what a variable is never changed from) whose result is
    -- checked.
    resultOf (Fix e) = case e of
        ParenExpr x                          -> resultOf x
        FunctionCall (Fix (VarExpr (L _ _ f))) args -> Just (f, args)
        VarExpr (L _ _ v) | Just x <- Map.lookup v (cxBound ctx) -> resultOf x
        _                                    -> Nothing
    -- Where what the call returns holds as the condition says, its
    -- out-parameters it stores to as it returns all of those aren't null.
    outsWhere (f, args) ivs = fromMaybe facts $ do
        os <- Map.lookup f (dOutSets (cxDecls ctx))
        return $ foldl' (\acc x -> setOne ctx x NotNull acc) facts
            [ var
            | k <- Set.toList (storedWhere os ivs)
            , Fix (UnaryExpr C.UopAddress var@(Fix (VarExpr (L _ _ x)))) : _ <- [drop k args]
            , Set.member x (cxOutVars ctx)
            ]

-- | A number written in the program, if an expression is one.
constOf :: C.Node (Lexeme Text) -> Maybe Integer
constOf (Fix e) = case e of
    ParenExpr x                        -> constOf x
    LiteralExpr C.Int (L _ _ t)        -> readMaybe (T.unpack t)
    LiteralExpr C.Bool (L _ _ "true")  -> Just 1
    LiteralExpr C.Bool (L _ _ "false") -> Just 0
    UnaryExpr C.UopMinus x             -> negate <$> constOf x
    _                                  -> Nothing

------------------------------------------------------------------------------
-- Changes
------------------------------------------------------------------------------

-- | Whether a path is in memory through a pointer, or an array's element.
throughMemory :: Path -> Bool
throughMemory = any memory . pathSteps
  where
    memory = \case
        Field _ -> False
        _       -> True

-- | Whether something else than the function's own assignments to it may
-- change a place: a call, or a store through a pointer.
changedElsewhere :: Ctx Text -> Path -> Bool
changedElsewhere ctx p = throughMemory p || Set.member (pathRoot p) (cxEscaped ctx)

forgetting :: (Entry -> Bool) -> Facts -> Facts
forgetting _ Unreached        = Unreached
forgetting gone (Facts facts) = Facts (Map.filter (not . gone) facts)

footOf :: Ctx Text -> C.Node (Lexeme Text) -> [Loc]
footOf ctx = maybe [LSomewhere] (footprint (cxEnv ctx) (cxTypes ctx) (reached ctx)) . pathOf

-- | Whether something else than the function can reach a variable: a
-- global, one whose address is taken, or an array.
reached :: Ctx Text -> Text -> Bool
reached ctx v = Set.member v (cxEscaped ctx) || maybe False (not . null . ctDims . resolveType (cxEnv ctx)) (Map.lookup v (cxTypes ctx))

-- | What a call may change: what it may store to.
called :: Ctx Text -> C.Node (Lexeme Text) -> [C.Node (Lexeme Text)] -> Facts -> Facts
called ctx f args = forgetting (mayChange (cxSummaries ctx) (callEffects (cxSummaries ctx) (cxTypes ctx) (reached ctx) (const Nothing) f args) . enFoot)

-- | A store of a pointer that may be null or not to a place: what depends
-- on the place, or may be it, is forgotten.
store :: Ctx Text -> C.Node (Lexeme Text) -> Null -> Facts -> Facts
store _ _ _ Unreached = Unreached
store ctx lhs s facts = case pathOf lhs of
    Just q ->
        let forgotten = forgetting (\en -> enPath en /= q && (dependsOn q (enPath en) || storedTo en)) facts
            shape = shapeOf ctx lhs
        in if null shape then forgotten else setEntry (Entry s (declaredNull shape) q (footOf ctx lhs)) forgotten
    Nothing -> forgetting storedTo facts
  where
    -- A variable's paths, and paths with it as an index; a place's parts.
    dependsOn q p
        | null (pathSteps q) = pathRoot q `elem` pathVars p
        | otherwise = p `isPartOf` q
    -- What else the store may be to: the same field through another
    -- pointer, or an object of the same type; nothing else, for one of the
    -- function's own variables. Where it's to can't be told, anything in
    -- memory.
    storedTo en = case storeAt (cxSummaries ctx) (cxTypes ctx) (reached ctx) lhs of
        Just e  -> mayChange (cxSummaries ctx) e (enFoot en)
        Nothing -> not (isJust (pathOf lhs)) && changedElsewhere ctx (enPath en)

------------------------------------------------------------------------------
-- Checks
------------------------------------------------------------------------------

data Failure = Failure
    { flLoc    :: Maybe (Lexeme Text)
    , flWhat   :: Text
    , flUse    :: NullUse
    , flSurely :: Bool
    }
    deriving (Eq, Ord)

type Walked = (Facts, [Failure])

-- | A pointer that must not be null: reported if it may be, and not null
-- after.
required :: Ctx Text -> NullUse -> C.Node (Lexeme Text) -> Walked -> Walked
required _ _ _ done@(Unreached, _) = done
required ctx use e (fs@(Facts facts), errs) =
    let now = case valueOf ctx facts e of
            MaybeNull | nonEmpty ctx e || countedHas ctx e || storedByCall ctx e -> NotNull
            v                                              -> v
    in ( setNull ctx e NotNull fs
       , errs ++ [ Failure (getLexeme e) (showNodePlain e) use (now == IsNull) | now /= NotNull ] )

-- | Whether a buffer's length (or count) is known to be at least 1.
nonEmpty :: Ctx Text -> C.Node (Lexeme Text) -> Bool
nonEmpty ctx e = any (maybe False (>= 1) . cxLeast ctx (C.lexemePosn <$> getLexeme e)) (lengthsOf ctx e)

-- | Whether a pointer is what a call stored through its address, where
-- the result it's kept in can only be what the call returns once it has.
storedByCall :: Ctx Text -> C.Node (Lexeme Text) -> Bool
storedByCall ctx e = fromMaybe False $ do
    Fix (VarExpr (L _ _ x)) <- Just (checkedPlace e)
    (f, k, v) <- Map.lookup x (cxOutCalls ctx)
    os <- Map.lookup f (dOutSets (cxDecls ctx))
    let pos = C.lexemePosn <$> getLexeme e
    return (Set.member k (storedWhere os [(cxLeast ctx pos v, cxMost ctx pos v)]))

-- | Whether a counted buffer has an element: where it does, it isn't null,
-- since nullptr has none and what may be null isn't stored to one.
countedHas :: Ctx Text -> C.Node (Lexeme Text) -> Bool
countedHas ctx e = counted e && maybe False (>= 1) (cxElements ctx e)
  where
    counted (Fix node) = case node of
        ParenExpr x       -> counted x
        VarExpr (L _ _ v) -> Map.member v (cxLengths ctx)
        _                 -> isJust (countedField ctx e)

-- | The field a counted buffer is in: one a count says how many elements
-- it has. What's stored to it may be nullptr (its count is then 0, which
-- the analysis of buffer sizes checks), but not what may be null.
countedField :: Ctx Text -> C.Node (Lexeme Text) -> Maybe Text
countedField ctx (Fix node) = case node of
    ParenExpr x               -> countedField ctx x
    PointerAccess b (L _ _ f) -> field b f
    MemberAccess b (L _ _ f)  -> field b f
    _                         -> Nothing
  where
    field b f = do
        st <- structOf ctx b
        f <$ guard (any ((== f) . fpBuffer) (Map.findWithDefault [] st (envPairs (cxEnv ctx))))

-- | The places that say how long a buffer is (or how much of it is used),
-- where the function can't have changed either.
lengthsOf :: Ctx Text -> C.Node (Lexeme Text) -> [Text]
lengthsOf ctx (Fix node) = case node of
    ParenExpr x               -> lengthsOf ctx x
    VarExpr (L _ _ v)         -> toList (Map.lookup v (cxLengths ctx))
    PointerAccess b (L _ _ f) -> field (PointerAccess b) b f
    MemberAccess b (L _ _ f)  -> field (MemberAccess b) b f
    _                         -> []
  where
    field access b f =
        [ pathName p
        | Just t <- [exprType ctx b]
        , fp <- Map.findWithDefault [] (ctName (resolveType (cxEnv ctx) t)) (envPairs (cxEnv ctx))
        , fpBuffer fp == f
        , len <- fpLength fp : toList (fpCount fp)
        , not (any (`Set.member` cxStored ctx) [f, fpLength fp, len])
        , Just p <- [pathOf (Fix (access (L (C.AlexPn 0 0 0) C.IdVar len)))]
        ]

-- | Evaluates expressions in order, from what's known before them.
walkAll :: Ctx Text -> Facts -> [C.Node (Lexeme Text)] -> Walked
walkAll ctx facts = foldl (\(fs, errs) x -> (++) errs <$> walk ctx fs x) (facts, [])

walk :: Ctx Text -> Facts -> C.Node (Lexeme Text) -> Walked
walk _ Unreached _ = (Unreached, [])
walk ctx facts (Fix node) = case node of
    SizeofExpr _ -> (facts, [])
    UnaryExpr C.UopDeref x -> required ctx Dereferenced x (walk ctx facts x)
    PointerAccess x _ -> required ctx Dereferenced x (walk ctx facts x)
    ArrayAccess x i -> required ctx Dereferenced x (walkAll ctx facts [x, i])
    UnaryExpr C.UopAddress x -> place facts x
    UnaryExpr o x | o `elem` [C.UopIncr, C.UopDecr] -> place facts x
    AssignExpr lhs op rhs ->
        let (fs, errs) = place facts lhs `andThen` \fs' -> walk ctx fs' rhs
        in (++) errs <$> assign fs lhs op rhs
    BinaryExpr a C.BopAnd b ->
        let (fa, ea) = walk ctx facts a
            (fb, eb) = walk ctx (narrow ctx True a fa) b
        in (joinFacts (narrow ctx False a fa) fb, ea ++ eb)
    BinaryExpr a C.BopOr b ->
        let (fa, ea) = walk ctx facts a
            (fb, eb) = walk ctx (narrow ctx False a fa) b
        in (joinFacts (narrow ctx True a fa) fb, ea ++ eb)
    TernaryExpr c a b ->
        let (fc, ec) = walk ctx facts c
            (fa, ea) = walk ctx (narrow ctx True c fc) a
            (fb, eb) = walk ctx (narrow ctx False c fc) b
        in (joinFacts fa fb, ec ++ ea ++ eb)
    FunctionCall (Fix (VarExpr (L _ _ f))) args | isStatement f -> walkAll ctx facts args
    -- A macro the program defines is what it expands to, reported where
    -- it's used.
    FunctionCall (Fix (LiteralExpr C.ConstId l@(L _ _ m))) args | Just body <- expandIn (cxSummaries ctx) m args ->
        map (\fl -> fl { flLoc = Just l }) <$> walk ctx facts body
    FunctionCall f args ->
        let callee = case f of
                Fix (VarExpr (L _ _ v)) | not (isVariable ctx v) -> (facts, [])
                -- A macro.
                Fix (LiteralExpr C.ConstId _) -> (facts, [])
                _ -> required ctx Called f (walk ctx facts f)
            (fs, errs) = callee `andThen` \fs0 -> walkAll ctx fs0 args
            contract = contractOf ctx f
            name = case f of
                Fix (VarExpr (L _ _ n)) -> n
                _                       -> showNodePlain f
            given = [ (k, arg) | Just c <- [contract], (k, arg, Just (DeclNonnull : _)) <- zip3 [1 ..] args (coParams c ++ repeat Nothing) ]
            (fs', errs') = foldl (\acc (k, arg) -> required ctx (ArgumentOf name k) arg acc) (fs, errs) given
        in (called ctx f args fs', errs')
    -- A statement in a macro, or a branch in one: as in a function.
    CompoundStmt stmts -> foldl (\(fs, errs) stmt -> (++) errs <$> stepStmt ctx fs stmt) (facts, []) stmts
    IfStmt c t e ->
        let (fc, ec) = walk ctx facts c
            (ft, et) = walk ctx (narrow ctx True c fc) t
            (fe, ee) = maybe (narrow ctx False c fc, []) (walk ctx (narrow ctx False c fc)) e
        in (joinFacts ft fe, ec ++ et ++ ee)
    _ -> walkAll ctx facts (toList node)
  where
    andThen (fs, errs) k = (++) errs <$> k fs
    -- An assignment's target, or what an address is taken of: evaluated,
    -- but not read.
    place fs x@(Fix n) = case n of
        ParenExpr y      -> place fs y
        MemberAccess y _ -> place fs y
        VarExpr _        -> (fs, [])
        _                -> walk ctx fs x
    -- A counted buffer, null only where it has no elements: stored to
    -- another with its length, which the analysis of buffer sizes checks.
    counted (Fix x) = case x of
        ParenExpr y       -> counted y
        CastExpr _ y      -> counted y
        VarExpr (L _ _ v) -> Map.member v (cxLengths ctx)
        _                 -> isJust (countedField ctx (Fix x))
    assign Unreached _ _ _ = (Unreached, [])
    assign fs@(Facts m) lhs op rhs =
        let now = if op == C.AopEq then valueOf ctx m rhs else valueOf ctx m lhs
            -- A name stored to that isn't a variable is the library's
            -- (errno): not a function, and not declared here.
            declared = case lhs of
                Fix (VarExpr (L _ _ v)) | not (isVariable ctx v) -> []
                _                                               -> shapeOf ctx lhs
            nonnull = op == C.AopEq && (declaredNull declared == NotNull || (isJust (countedField ctx lhs) && now == MaybeNull && not (counted rhs)))
            (fs', errs) = if nonnull then required ctx (StoredIn (showNodePlain lhs)) rhs (fs, []) else (fs, [])
        in (store ctx lhs (if nonnull then NotNull else now) fs', errs)

-- | Calls that are statements of what holds, which change nothing: the
-- CFG's for a branch, or an assert.
isStatement :: Text -> Bool
isStatement f = "__tokstyle_" `T.isPrefixOf` f || f == "assert"

stepStmt :: Ctx Text -> Facts -> C.Node (Lexeme Text) -> Walked
stepStmt _ Unreached _ = (Unreached, [])
stepStmt ctx facts stmt@(Fix node) = case node of
    -- A branch's condition is evaluated in the block before it.
    ExprStmt (Fix (FunctionCall (Fix (VarExpr (L _ _ f))) [c]))
        | f == "__tokstyle_assume_true" -> (narrow ctx True c facts, [])
        | f == "__tokstyle_assume_false" -> (narrow ctx False c facts, [])
        | f == "assert" -> narrow ctx True c <$$> walk ctx facts c
    -- An array is no pointer: what it's initialised with is its elements.
    VarDeclStmt (Fix (VarDecl _ _ (_ : _))) mInit -> maybe (facts, []) (walk ctx facts) mInit
    VarDeclStmt (Fix (VarDecl _ l@(L _ _ v) _)) mInit ->
        let var = Fix (VarExpr l)
        in case mInit of
            Nothing -> (forgetting (\en -> v `elem` pathVars (enPath en)) facts, [])
            Just ini ->
                let (fs, errs) = walk ctx facts ini
                in case fs of
                    Unreached -> (Unreached, errs)
                    Facts m ->
                        let now = valueOf ctx m ini
                            nonnull = declaredNull (shapeOf ctx var) == NotNull
                            (fs', errs') = if nonnull then required ctx (StoredIn v) ini (fs, errs) else (fs, errs)
                        in (store ctx var (if nonnull then NotNull else now) fs', errs')
    Return (Just e) ->
        let (fs, errs) = walk ctx facts e
        in if declaredNull (cxReturn ctx) == NotNull then required ctx (ReturnedFrom (cxName ctx)) e (fs, errs) else (fs, errs)
    _ -> walk ctx facts stmt
  where
    f <$$> (fs, errs) = (f fs, errs)

-- | Each place in a function where a pointer that may be null is used as
-- one that must not be.
failuresOf :: Ctx Text -> Map (Int, Int) Known -> C.Node (Lexeme Text) -> [Failure]
failuresOf ctx least defn =
    let cfg0 = runIdentity (buildCFG ctx defn (Facts Map.empty))
        cfg = fst (runIdentity (fixpoint ctx (cxName ctx) cfg0))
        before = storedBefore cfg
        block n = concat (snd (mapAccumL (step (cfgNodeId n)) (cfgInFacts n, Map.findWithDefault Set.empty (cfgNodeId n) before) (zip [0 ..] (cfgStmts n))))
        step k (fs, stored) (i, stmt) =
            let stored' = stored <> snd (changedIn stmt)
                known = Map.lookup (k, i) least
                (fs', errs) = stepStmt ctx { cxLeast = maybe (\_ _ -> Nothing) knownLeast known
                                           , cxMost = maybe (\_ _ -> Nothing) knownMost known
                                           , cxElements = maybe (const Nothing) knownElements known
                                           , cxStored = stored' } fs stmt
            in ((fs', stored'), errs)
    in nubOrd (concatMap block (Map.elems cfg))

-- | The fields a function may have stored to before each block: on some
-- way to it from the start.
storedBefore :: CFG Text a -> Map Int (Set.Set Text)
storedBefore cfg = go (Set.empty <$ cfg)
  where
    own = foldMap (snd . changedIn) . cfgStmts <$> cfg
    go ins =
        let ins' = (\n -> foldMap (\p -> Map.findWithDefault Set.empty p ins <> Map.findWithDefault Set.empty p own) (cfgPreds n)) <$> cfg
        in if ins' == ins then ins else go ins'

-- | What each function returning only numbers stores through its
-- out-parameters as it returns each: those it has stored a pointer that
-- isn't null through at every return of the number.
outSetsIn :: [(Ctx Text, Map (Int, Int) Known, C.Node (Lexeme Text))] -> Map Text OutSets
outSetsIn fns = Map.fromList
    [ (cxName ctx, OutSets returns)
    | (ctx, least, defn@(Fix (FunctionDefn _ (Fix (FunctionPrototype _ _ params)) _))) <- fns
    , let names = [ p | Fix (VarDecl _ (L _ _ p) _) <- params ]
          outs = [ (k, p) | (k, p) <- zip [0 ..] names, maybe False ((>= 2) . ctPointers) (Map.lookup p (cxTypes ctx)) ]
    , not (null outs)
    -- What its out-parameters point to is looked at as declared neither
    -- way: what the caller gives may be null, whatever they say.
    , let open = foldl' (\m (_, p) -> Map.adjust (\case o : _ : rest -> o : DeclUnspecified : rest; sh -> sh) p m) (cxShapes ctx) outs
          stored fs p = case fs of
              Unreached -> True
              Facts m   -> maybe False ((== NotNull) . enNow) (pathOf (Fix (UnaryExpr C.UopDeref (Fix (VarExpr (L (C.AlexPn 0 0 0) C.IdVar p))))) >>= (`Map.lookup` m) . pathName)
          returns = [ (returned known e, Set.fromList [ k | (k, p) <- outs, stored fs p ]) | (fs, e, known) <- returnsIn ctx { cxShapes = open } least defn ]
    , any (not . Set.null . snd) returns
    ]
  where
    returned known e = case constOf e of
        Just c -> (Just c, Just c)
        Nothing -> case unFix (checkedPlace e) of
            VarExpr (L pos _ v) | Just kn <- known -> (knownLeast kn (Just pos) v, knownMost kn (Just pos) v)
            _ -> (Nothing, Nothing)

-- | What's known where a function returns, with what it returns and what
-- the analysis of buffer sizes knows of integers there.
returnsIn :: Ctx Text -> Map (Int, Int) Known -> C.Node (Lexeme Text) -> [(Facts, C.Node (Lexeme Text), Maybe Known)]
returnsIn ctx least defn =
    let cfg0 = runIdentity (buildCFG ctx defn (Facts Map.empty))
        cfg = fst (runIdentity (fixpoint ctx (cxName ctx) cfg0))
        block n = snd (mapAccumL (step (cfgNodeId n)) (cfgInFacts n) (zip [0 ..] (cfgStmts n)))
        step k fs (i, stmt) = (fst (stepStmt ctx fs stmt), case unFix stmt of
            Return (Just e) -> Just (fs, e, Map.lookup (k, i) least)
            _               -> Nothing)
    in catMaybes (concatMap block (Map.elems cfg))

-- | Fields stored only together with others on the same object, in
-- statements next to each other with no call between them, where the
-- others aren't null if the first may not be: once the first isn't null,
-- neither are they. What the program starts with zeroed has them all null.
besideIn :: [(Ctx Text, C.Node (Lexeme Text))] -> Map (Text, Text) [Text]
besideIn fns = Map.filter (not . null) $ Map.mapWithKey (\k os -> filter (holds k) (Set.toList os)) candidates
  where
    stores = concatMap storesIn fns
    candidates = Map.fromListWith (<>)
        [ ((st, f), Map.keysSet (Map.delete f run)) | (Just st, f, Just run) <- stores ]
    -- A store to a field of a struct that isn't known may be to any.
    to st f (st', f', _) = f' == f && maybe True (== st) st'
    holds (st, c) o =
        and [ maybe False (\run -> Map.member o run && (Map.lookup c run == Just IsNull || Map.lookup o run == Just NotNull)) r | x@(_, _, r) <- stores, to st c x ]
        && and [ maybe False (Map.member c) r | x@(_, _, r) <- stores, to st o x ]
    -- Every store to a field, with what's stored to the object's other
    -- fields next to it (and to it), if it's a plain one.
    storesIn (ctx, defn) =
        let runs = Map.unions (map (runIn ctx) [ ss | Fix (CompoundStmt ss) <- subnodes defn ])
        in [ (structOf ctx b, f, Map.lookup p runs) | (b, f, p) <- concatMap fieldsWritten (subnodes defn) ]
    fieldsWritten (Fix node) = case node of
        AssignExpr lhs _ _                              -> field lhs
        UnaryExpr C.UopAddress x                        -> field x
        UnaryExpr o x | o `elem` [C.UopIncr, C.UopDecr] -> field x
        _                                               -> []
    field (Fix x) = case x of
        PointerAccess b (L p _ f) -> [(b, f, p)]
        MemberAccess b (L p _ f)  -> [(b, f, p)]
        ParenExpr y               -> field y
        _                         -> []
    -- Statements storing to fields with no call: by each field's place in
    -- the source, what's stored to the fields of the same object there.
    runIn ctx ss = Map.unions
        [ Map.fromList [ (p, Map.fromList [ (f, v) | (b', _, f, v) <- run, b' == b ]) | (b, p, _, _) <- run ]
        | run <- runsOf (map (plainStore ctx) ss) ]
    runsOf xs = case break isJust xs of
        (_, [])  -> []
        (_, ys) -> let (run, rest) = span isJust ys in catMaybes run : runsOf rest
    plainStore ctx (Fix st) = case st of
        ExprStmt (Fix (AssignExpr (Fix lhs) C.AopEq rhs)) | not (any isCall (subnodes rhs)) -> case lhs of
            PointerAccess b (L p _ f) -> Just (showNodePlain b, p, f, valueOf ctx Map.empty rhs)
            MemberAccess b (L p _ f)  -> Just (showNodePlain b, p, f, valueOf ctx Map.empty rhs)
            _                         -> Nothing
        _ -> Nothing
    isCall (Fix n) = case n of
        FunctionCall{} -> True
        _              -> False

-- | Checks every use of a pointer that must not be null, with what the
-- analysis of buffer sizes knows of integers.
checkNullability :: Sizes -> [(FilePath, [C.Node (Lexeme Text)])] -> [ErrorInfo p]
checkNullability sizes parsed =
    let files = scopeMacros parsed
        nodes = concatMap snd files
        env = collectEnv nodes
        decls0 = declsOf nodes
        fns0 = [ (ctx, Map.findWithDefault Map.empty (file, loc) least, defn) | (file, ns) <- files, (ctx, loc, defn) <- concatMap (functionsIn env decls0 summaries) ns ]
        decls = decls0 { dBeside = besideIn [ (ctx, defn) | (ctx, _, defn) <- fns0 ], dOutSets = outSetsIn fns0 }
        least = leastBefore sizes
        summaries = sizeSummaries sizes
    in [ ErrorInfo (flLoc fl) [InFile file] (MayBeNull (flWhat fl) (flUse fl) (flSurely fl)) []
       | (file, ns) <- files
       , (ctx, loc, defn) <- concatMap (functionsIn env decls summaries) ns
       , fl <- failuresOf ctx (Map.findWithDefault Map.empty (file, loc) least) defn
       ]
