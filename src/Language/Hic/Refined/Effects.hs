{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

-- | Where each function may store, so what's known of memory can be kept
-- across a call that can't change it.
--
-- A store is to a field of a struct, to an object of a type through a
-- pointer, to a variable something else can reach, or through a
-- parameter (to what each call gives it). A pointer of a type may point to
-- any object of the type, to a variable of it something else can reach,
-- and to a field of it only where the program takes the field's address
-- (or it's an array).
-- A function may store where its own statements do and where everything
-- it calls may: worked out round the call graph until nothing changes.
--
-- What isn't in the program is trusted as follows. A function from a
-- library or the operating system (one the program doesn't declare) stores
-- only through the pointers it's given; one the program declares but
-- doesn't define where it's looked at may do anything. A call through a
-- pointer is to one of the program's functions
-- given as that type; if there are none, it's the client's, which may call
-- the public API and so change anything, but for callbacks the API says
-- may not call back ('callsNothingBack').
module Language.Hic.Refined.Effects
    ( Loc (..)
    , Effects (..)
    , Summaries
    , summarise
    , expandIn
    , scopeMacros
    , mayChange
    , storeAt
    , footprint
    , callEffects
    , ownArrayIn
    , targetsOf
    , bytesThrough
    , rawStructs
    ) where

import qualified Control.Monad.State.Strict              as State
import           Data.Fix                                (Fix (..))
import           Data.Foldable                           (toList)
import           Data.List                               (elemIndex, mapAccumL)
import           Data.Map.Strict                         (Map)
import qualified Data.Map.Strict                         as Map
import           Data.Maybe                              (fromMaybe, isJust,
                                                          mapMaybe)
import           Data.Set                                (Set)
import qualified Data.Set                                as Set
import           Data.Text                               (Text)
import qualified Data.Text                               as T
import           Language.Cimple                         (Lexeme (..),
                                                          NodeF (..))
import qualified Language.Cimple                         as C
import           Language.Hic.Refined.BufferSize.Env     (CType (..), Env (..),
                                                          Param (..),
                                                          Signature (..),
                                                          declType, integerType,
                                                          isPointerType,
                                                          localsOf, resolveType,
                                                          subnodes, typeOfDecl,
                                                          typeOfExpr)
import           Language.Hic.Refined.BufferSize.Paths   (Path (..), Step (..),
                                                          pathOf)
import qualified Language.Hic.Refined.Inference.Platform as Platform

-- | A type as far as stores go: its name and how many pointers deep it is.
-- An array is its elements, and the byte types are one.
type TypeKey = (Text, Int)

typeKey :: Env -> CType -> TypeKey
typeKey env t =
    let t' = resolveType env t
        name = if ctName t' `elem` ["char", "uint8_t", "int8_t"] then "byte" else ctName t'
    in (name, ctPointers t')

-- | A place a store may be to.
data Loc
    = LField Text Text TypeKey
      -- ^ A field of a struct, and its type.
    | LObject TypeKey
      -- ^ An object of a type, through a pointer.
    | LVar Text TypeKey
      -- ^ A variable something else can reach, and its type: a global, or
      -- one whose address is kept (an array's is, wherever it's put).
    | LOwn Text
      -- ^ An array of a function's own nothing else can reach: only calls
      -- given it change it.
    | LParam Int
      -- ^ What a function's pointer parameter (by position) points to,
      -- where the function doesn't change the parameter: whatever a call
      -- gives it.
    | LSomewhere
      -- ^ In a place's footprint: on the way to it is something of a type
      -- that isn't known, which any store may change.
    deriving (Show, Eq, Ord)

data Effects
    = Anything
    | Only Stores
    deriving (Show, Eq)

-- | Where stores are to, by what a place's footprint is looked up with.
data Stores = Stores
    { stFields  :: Set (Text, Text)
      -- ^ Fields, by struct and name.
    , stObjects :: Set TypeKey
      -- ^ Objects of these types, through pointers.
    , stVars    :: Set Text
    , stTypes   :: Set TypeKey
      -- ^ The types of the fields whose address is taken and the variables
      -- stored to, which a pointer of the type may be to.
    , stParams  :: Set Int
    }
    deriving (Show, Eq)

instance Semigroup Effects where
    Only a <> Only b = Only (Stores (u stFields) (u stObjects) (u stVars) (u stTypes) (u stParams))
      where
        u :: Ord x => (Stores -> Set x) -> Set x
        u field = Set.union (field a) (field b)
    _ <> _           = Anything

instance Monoid Effects where
    mempty = Only (Stores Set.empty Set.empty Set.empty Set.empty Set.empty)

-- | A store to one place.
single :: Summaries -> Loc -> Effects
single sm = \case
    LField st f t -> Only none { stFields = Set.singleton (st, f), stTypes = if addressable sm st f then Set.singleton t else Set.empty }
    LObject t     -> Only none { stObjects = Set.singleton t }
    LVar v t      -> Only none { stVars = Set.singleton v, stTypes = Set.singleton t }
    LOwn v        -> Only none { stVars = Set.singleton v }
    LParam k      -> Only none { stParams = Set.singleton k }
    LSomewhere    -> Anything
  where
    none = Stores Set.empty Set.empty Set.empty Set.empty Set.empty

-- | Whether a pointer may be to a field: if its address is taken.
addressable :: Summaries -> Text -> Text -> Bool
addressable sm st f = Set.member (st, f) (smAddressable sm)

-- | Whether stores may change a place, given the places it's in (its
-- 'footprint'). One that's in none is a function's own variable, which
-- nothing else can change, and one in its own array only a call given
-- that changes ('ownArrayIn').
mayChange :: Summaries -> Effects -> [Loc] -> Bool
mayChange _ Anything foot = any (\case LOwn{} -> False; _ -> True) foot
mayChange sm (Only st) foot = any hit foot
  where
    -- Bytes written where the type isn't known reach what bytes may be
    -- written to.
    bytes = Set.member ("void", 0) (stObjects st) || Set.member ("byte", 0) (stObjects st)
    raw t = bytes && (t == ("byte", 0) || Set.member t (smRaw sm))
    hit = \case
        LField s f t -> Set.member (s, f) (stFields st) || (addressable sm s f && (Set.member t (stObjects st) || raw t)) || raw (s, 0)
        LObject t    -> Set.member t (stObjects st) || Set.member t (stTypes st) || raw t
        LVar v t     -> Set.member v (stVars st) || Set.member t (stObjects st) || raw t
        LOwn v       -> Set.member v (stVars st)
        LParam _     -> False
        LSomewhere   -> st /= Stores Set.empty Set.empty Set.empty Set.empty Set.empty

------------------------------------------------------------------------------
-- Macros
------------------------------------------------------------------------------

-- | Macros with parameters: their parameters, whether they take more, and
-- their bodies.
type Macros = Map Text ([Text], Bool, C.Node (Lexeme Text))

macros :: [C.Node (Lexeme Text)] -> Macros
macros nodes = Map.fromList
    [ (name, ([ p | Fix (MacroParam (L _ _ p)) <- params ], any isEllipsis params, body))
    | Fix (PreprocDefineMacro (L _ _ name) params body) <- concatMap subnodes nodes ]
  where
    isEllipsis (Fix Ellipsis) = True
    isEllipsis _              = False

-- | Files where each macro the program defines again has a name of its
-- own, and so do its uses until it's undefined or the file ends: a macro
-- is what it's defined as where it's used.
scopeMacros :: [(FilePath, [C.Node (Lexeme Text)])] -> [(FilePath, [C.Node (Lexeme Text)])]
scopeMacros = snd . mapAccumL file Map.empty
  where
    file seen (path, nodes) =
        let (nodes', (seen', _)) = State.runState (traverse go nodes) (seen, Map.empty)
        in (seen', (path, nodes'))
    -- The definitions so far in the program, and each macro's name here.
    go :: C.Node (Lexeme Text) -> State.State (Map Text Int, Map Text Text) (C.Node (Lexeme Text))
    go (Fix node) = case node of
        PreprocDefineMacro (L p c name) params body -> do
            (seen, current) <- State.get
            let n = Map.findWithDefault 0 name seen
                name' = if n == 0 then name else name <> "#" <> T.pack (show (n + 1 :: Int))
            State.put (Map.insert name (n + 1) seen, Map.insert name name' current)
            Fix . PreprocDefineMacro (L p c name') params <$> go body
        PreprocUndef (L p c name) -> do
            (seen, current) <- State.get
            State.put (seen, Map.delete name current)
            return (Fix (PreprocUndef (L p c (Map.findWithDefault name name current))))
        LiteralExpr C.ConstId (L p c name) -> do
            current <- State.gets snd
            return (Fix (LiteralExpr C.ConstId (L p c (Map.findWithDefault name name current))))
        _ -> Fix <$> traverse go node

-- | A macro call as what it expands to, if the program defines the macro.
expandIn :: Summaries -> Text -> [C.Node (Lexeme Text)] -> Maybe (C.Node (Lexeme Text))
expandIn = expandMacro . smMacros

-- | A macro's body with a call's arguments in place of its parameters.
expandMacro :: Macros -> Text -> [C.Node (Lexeme Text)] -> Maybe (C.Node (Lexeme Text))
expandMacro ms name args = do
    (params, variadic, body) <- Map.lookup name ms
    let given = Map.fromList (zip params args)
        rest = drop (length params) args
        go (Fix node) = case node of
            VarExpr (L _ _ v) | Just a <- Map.lookup v given -> a
            FunctionCall f as -> Fix (FunctionCall (go f) (concatMap spread as))
            _ -> Fix (fmap go node)
        spread a
            | variadic, isVaArgs a = rest
            | otherwise = [go a]
        isVaArgs (Fix a) = case a of
            VarExpr (L _ _ "__VA_ARGS__")               -> True
            LiteralExpr C.ConstId (L _ _ "__VA_ARGS__") -> True
            _                                           -> False
    return (go body)

------------------------------------------------------------------------------
-- Summaries
------------------------------------------------------------------------------

data Summaries = Summaries
    { smEnv         :: Env
    , smFunctions   :: Map Text Effects
    , smTargets     :: Map Text [Text]
      -- ^ For each function type, the program's functions given as one.
    , smMacros      :: Macros
    , smAddressable :: Set (Text, Text)
      -- ^ Fields a pointer may be to, by struct and name: those whose
      -- address the program takes, and arrays.
    , smUnseen      :: Set Text
      -- ^ Functions the program declares but doesn't define where it's
      -- looked at, which may do anything.
    , smBytes       :: Map Text (Set Int)
      -- ^ The pointer parameters (by position) each function may write
      -- bytes through: copy or set them, store through them other than to
      -- a field, or give them to something else.
    , smKeptWritten :: Bool
      -- ^ Whether bytes may be written through a pointer kept as a
      -- @void *@: by a callback given it, or straight through where it's
      -- kept.
    , smRaw         :: Set TypeKey
      -- ^ The types whose objects bytes may be written to: those a pointer
      -- to is made a pointer to something else where bytes may be written
      -- through it, and the structs in them.
    }

-- | A function as its stores are worked out.
data Function = Function
    { fnName   :: Text
    , fnParams :: [Text]
    , fnTypes  :: Map Text CType
    , fnBody   :: C.Node (Lexeme Text)
    }

functionsOf :: Env -> C.Node (Lexeme Text) -> [Function]
functionsOf env (Fix node) = case node of
    FunctionDefn _ (Fix (FunctionPrototype _ (L _ _ name) params)) body ->
        let own = mapMaybe (declType env) params
            ownTypes = Map.fromList own
            locals = Map.fromList (localsOf env (ownTypes <> envGlobals env) body)
        in [Function name (map fst own) (Map.unions [locals, ownTypes, envGlobals env]) body]
    FunctionDefn{} -> []
    _ -> concatMap (functionsOf env) (toList node)

summarise :: Env -> [C.Node (Lexeme Text)] -> Summaries
summarise env nodes =
    let fns = concatMap (functionsOf env) nodes
        defined = Set.fromList (map fnName fns)
        asValues = Set.fromList
            [ v | n <- nodes, v <- valuesIn n, Set.member v defined ]
        protos = Map.fromListWith (\_ old -> old)
            [ (name, protoType env ret params) | Fix (FunctionPrototype ret (L _ _ name) params) <- concatMap subnodes nodes ]
        typedefs = Set.fromList [ t | Fix (TypedefFunction (Fix (FunctionPrototype _ (L _ _ t) _))) <- concatMap subnodes nodes ]
        targets = Map.fromList
            [ (t, [ f | f <- Set.toList asValues, Map.lookup f protos == Just ty ])
            | t <- Set.toList typedefs, Just ty <- [Map.lookup t protos] ]
        declared = Set.fromList [ f | Fix (FunctionDecl _ (Fix (FunctionPrototype _ (L _ _ f) _))) <- concatMap subnodes nodes ]
        addressed = Set.fromList
            [ (ctName (resolveType env t), f)
            | fn <- fns
            , Fix (UnaryExpr C.UopAddress x) <- subnodes (fnBody fn)
            , (b, f, through) <- fieldOf (stripped x)
            , Just t0 <- [typeOfExpr env (fnTypes fn) b]
            , let t = if through then elementOf (resolveType env t0) else t0
            ]
        arrays = Set.fromList [ (st, f) | (st, fields) <- Map.toList (envStructs env), (f, ft) <- Map.toList fields, not (null (ctDims ft)) ]
        start = Summaries env (Map.fromList [ (f, mempty) | f <- Set.toList defined ]) targets (macros nodes) (addressed <> arrays) (declared `Set.difference` defined)
            (Map.fromList [ (f, Set.empty) | f <- Set.toList defined ]) False Set.empty
        prepared = [ (fn, prepare start fn) | fn <- fns ]
        stored = go (64 :: Int) prepared start
        preparedBytes = [ (fn, prepareBytes start fn) | fn <- fns ]
        -- A pointer kept as a @void *@ (in a field or a global) can only be
        -- written through by a callback it's given back to: if none writes
        -- bytes through what it's given there, that's nothing.
        withoutKept = bytesRound (64 :: Int) [ (fnName fn, (own, calls, ps)) | (fn, (own, _, calls, ps)) <- preparedBytes ] stored
        keptGiven = Set.fromList
            [ (ctName (resolveType env t), j)
            | fn <- fns
            , Fix (FunctionCall f args) <- subnodes (fnBody fn)
            , case f of
                Fix (VarExpr (L _ _ g)) -> Map.member g (fnTypes fn)
                Fix LiteralExpr{}       -> False
                _                       -> True
            , Just t <- [typeOfExpr env (fnTypes fn) f]
            , (j, arg) <- zip [0 ..] args
            , isKept (fnTypes fn) (stripped arg)
            ]
        isKept types x = isVoidPointer types x && case unFix x of
            PointerAccess{}   -> True
            MemberAccess{}    -> True
            VarExpr (L _ _ v) -> isGlobal env types v
            _                 -> False
        isVoidPointer types x = case resolveType env <$> typeOfExpr env types x of
            Just t  -> ctName t == "void" && ctPointers t == 1 && null (ctDims t)
            Nothing -> False
        callbacksWrite = or
            [ Set.member j (Map.findWithDefault Set.empty g withoutKept)
            | (name, j) <- Set.toList keptGiven
            , g <- Map.findWithDefault [] name targets ]
            || any (Set.member keptParam) (Map.elems withoutKept)
        bytes
            | callbacksWrite = bytesRound (64 :: Int) [ (fnName fn, (own <> kept, calls, ps)) | (fn, (own, kept, calls, ps)) <- preparedBytes ] stored
            | otherwise = withoutKept
        withBytes = stored { smBytes = bytes, smKeptWritten = callbacksWrite }
    in withBytes { smRaw = rawTypes withBytes fns }
  where
    -- From none, round the call graph until nothing changes. A function
    -- still changing at the end may write bytes through all its pointers.
    bytesRound n prepared sm =
        let next = Map.fromListWith Set.union
                [ (name, own <> Set.fromList [ k | (k, check) <- calls, check sm ]) | (name, (own, calls, _)) <- prepared ]
            everyPointer = Map.fromListWith Set.union [ (name, ps) | (name, (_, _, ps)) <- prepared ]
        in if next == smBytes sm then next
           else if n <= 1 then Map.mapWithKey (\f ks -> if Map.lookup f (smBytes sm) == Just ks then ks else Map.findWithDefault ks f everyPointer) next
           else bytesRound (n - 1) prepared sm { smBytes = next }
    -- Round the call graph until nothing changes. A function still
    -- changing at the end may store anywhere.
    go n prepared sm =
        let next = Map.fromListWith (<>) [ (fnName fn, own <> foldMap (\call -> call sm) calls) | (fn, (own, calls)) <- prepared ]
            sm' = sm { smFunctions = next }
        in if next == smFunctions sm then sm
           else if n <= 1 then sm' { smFunctions = Map.mapWithKey (\f e -> if Map.lookup f (smFunctions sm) == Just e then e else Anything) next }
           else go (n - 1) prepared sm'
    -- The field an address is taken of: of a struct, or through a pointer.
    fieldOf (Fix x) = case x of
        MemberAccess b (L _ _ f)  -> [(b, f, False)]
        PointerAccess b (L _ _ f) -> [(b, f, True)]
        ArrayAccess b _           -> fieldOf (stripped b)
        _                         -> []
    -- Function names used other than as what a call calls.
    valuesIn (Fix node) = case node of
        FunctionCall (Fix (VarExpr _)) args -> concatMap valuesIn args
        VarExpr (L _ _ v)                   -> [v]
        _                                   -> concatMap valuesIn (toList node)

-- | A function's own stores, and its calls, which store where what they
-- call does: worked out once, as the summaries of what they call change.
-- A macro is what it expands to.
prepare :: Summaries -> Function -> (Effects, [Summaries -> Effects])
prepare sm fn = foldMap here (subnodes (fnBody fn))
  where
    env = smEnv sm
    types = fnTypes fn
    here (Fix node) = case node of
        AssignExpr lhs _ _ -> (store lhs, [])
        UnaryExpr o x | o `elem` [C.UopIncr, C.UopDecr] -> (store x, [])
        FunctionCall (Fix (LiteralExpr C.ConstId (L _ _ m))) args
            | Just body <- expandMacro (smMacros sm) m args -> foldMap here (subnodes body)
        FunctionCall f args -> (mempty, [\sm' -> callEffects sm' types (isGlobal env types) param f args])
        _ -> mempty
    store lhs = maybe mempty (single sm) (storeLoc env types (isGlobal env types) param lhs)
    -- The pointer parameters the function never changes.
    unchanged = Set.fromList [ v | v <- fnParams fn, maybe False isPointerType (resolveType env <$> Map.lookup v types) ]
        `Set.difference` Set.fromList [ v | Fix (AssignExpr (Fix (VarExpr (L _ _ v))) _ _) <- subnodes (fnBody fn) ]
        `Set.difference` Set.fromList [ v | Fix (UnaryExpr o (Fix (VarExpr (L _ _ v)))) <- subnodes (fnBody fn), o `elem` [C.UopIncr, C.UopDecr, C.UopAddress] ]
    param v
        | Set.member v unchanged = elemIndex v (fnParams fn)
        | otherwise = Nothing

-- | The pointer parameters a function writes bytes through itself, those
-- it keeps in a @void *@ (which only a callback given it could write
-- through), those it gives to calls (which may write bytes through them),
-- and all of them. A local pointer into a parameter is the parameter.
prepareBytes :: Summaries -> Function -> (Set Int, Set Int, [(Int, Summaries -> Bool)], Set Int)
prepareBytes sm fn = (Set.fromList written, Set.fromList kept, calls, Set.fromList (Map.elems pointers))
  where
    env = smEnv sm
    types = fnTypes fn
    pointers = Map.fromList
        [ (v, k) | (k, v) <- zip [0 ..] (fnParams fn), maybe False isPointerType (resolveType env <$> Map.lookup v types) ]
    -- A pointer kept as a @void *@ is read as this.
    keptRoot = "<kept>"
    index v = Set.toList (Map.findWithDefault Set.empty v aliases)
    nodes = expanded (fnBody fn)
    -- Every node, a macro as what it expands to.
    expanded n = n : case unFix n of
        FunctionCall (Fix (LiteralExpr C.ConstId (L _ _ m))) args
            | Just body <- expandMacro (smMacros sm) m args -> expanded body
        node -> concatMap expanded (toList node)
    -- The parameters each of the function's own pointers may be into.
    aliases = grow (Map.insert keptRoot (Set.singleton keptParam) (Map.map Set.singleton pointers))
      where
        grow m =
            let m' = Map.unionWith Set.union m $ Map.fromListWith Set.union
                    [ (v, ks) | (v, e) <- givenTo, let ks = Set.fromList (concatMap (\r -> Set.toList (Map.findWithDefault Set.empty r m)) (roots e)), not (Set.null ks) ]
            in if m' == m then m else grow m'
    givenTo = [ (v, e) | Fix node <- nodes, (v, e) <- case node of
        VarDeclStmt (Fix (VarDecl _ (L _ _ v) _)) (Just e) -> [(v, e)]
        AssignExpr (Fix (VarExpr (L _ _ v))) _ e | own v   -> [(v, e)]
        _                                                  -> [] ]
    own v = not (isGlobal env types v) && Map.member v types
    escapes = concatMap escapeOf nodes
    written = concatMap index ([ r | (False, r) <- escapes ] ++ concatMap storeOf nodes)
    kept = concatMap index [ r | (True, r) <- escapes ]
    -- Pointers stored somewhere other than the function's own variables,
    -- and whether that's a @void *@.
    escapeOf (Fix node) = case node of
        AssignExpr (Fix (VarExpr (L _ _ v))) _ _ | own v -> []
        AssignExpr lhs _ rhs -> map ((,) (isVoidPointer lhs)) (roots rhs)
        Return (Just e) -> map ((,) returnsVoidPointer) (roots e)
        InitialiserList es -> map ((,) False) (concatMap roots es)
        _ -> []
    isVoidPointer x = case resolveType env <$> typeOfExpr env types x of
        Just t  -> ctName t == "void" && ctPointers t == 1 && null (ctDims t)
        Nothing -> False
    -- Kept where it's a field or a global, or given back by a function
    -- (but for new memory from an allocator).
    isKeptRead = \case
        PointerAccess{}   -> True
        MemberAccess{}    -> True
        VarExpr (L _ _ v) -> isGlobal env types v
        FunctionCall f _  -> not (isAllocator f)
        _                 -> False
    isAllocator f = case unFix f of
        VarExpr (L _ _ name) | not (Map.member name types) -> Map.member name (envAllocSizes env)
        _ -> maybe False (\t -> Map.member (ctName (resolveType env t)) (envAllocSizes env)) (typeOfExpr env types f)
    -- A @void *@ given back is kept by the caller.
    returnsVoidPointer = maybe False (\sig -> let t = resolveType env (sigReturn sig) in ctName t == "void" && ctPointers t == 1)
        (Map.lookup (fnName fn) (envFunctions env))
    -- A struct stored whole is one of its type, as the pointer says.
    storeOf (Fix node) = case node of
        AssignExpr lhs _ _ | not (isStruct lhs)         -> storedThrough lhs
        UnaryExpr o x | o `elem` [C.UopIncr, C.UopDecr] -> storedThrough x
        _                                               -> []
    isStruct x = case resolveType env <$> typeOfExpr env types x of
        Just t -> ctPointers t == 0 && null (ctDims t) && Map.member (ctName t) (envStructs env)
        Nothing -> False
    calls =
        [ (k, \sm' -> bytesThrough sm' types g args j)
        | Fix (FunctionCall g args) <- nodes
        , case g of
            Fix (LiteralExpr C.ConstId _) -> False
            _                             -> True
        , (j, arg) <- zip [0 ..] args
        , k <- concatMap index (roots arg)
        ]
    -- The variables a pointer is into.
    roots e@(Fix node)
        | Just t <- typeOfExpr env types e, not (isPointerType (resolveType env t)) = []
        | isVoidPointer e, isKeptRead node = [keptRoot]
        | otherwise = case node of
            VarExpr (L _ _ v)                        -> [v]
            ParenExpr x                              -> roots x
            CastExpr _ x                             -> roots x
            BinaryExpr a o b | o `elem` [C.BopPlus, C.BopMinus] -> roots a ++ roots b
            TernaryExpr _ a b                        -> roots a ++ roots b
            UnaryExpr C.UopAddress x                 -> addressRoots x
            _                                        -> []
    addressRoots (Fix node) = case node of
        ParenExpr x            -> addressRoots x
        ArrayAccess b _        -> roots b
        UnaryExpr C.UopDeref x -> roots x
        _                      -> []
    -- What a store goes through, but not to a field.
    storedThrough (Fix node) = case node of
        ParenExpr x            -> storedThrough x
        ArrayAccess b _        -> roots b
        UnaryExpr C.UopDeref x -> roots x
        _                      -> []

-- | Whether a call may write bytes through what it's given at a position.
bytesThrough :: Summaries -> Map Text CType -> C.Node (Lexeme Text) -> [C.Node (Lexeme Text)] -> Int -> Bool
bytesThrough sm types f args j = case f of
    Fix (VarExpr (L _ _ name))
        | not (Map.member name types), Just ks <- Map.lookup name (smBytes sm) -> Set.member j ks
        | not (Map.member name types) -> external name
    Fix (LiteralExpr C.ConstId _) -> False
    _ -> case typeOfExpr (smEnv sm) types f of
        Just t | name <- ctName (resolveType (smEnv sm) t) ->
            -- The client's callbacks keep to the API: they write no bytes
            -- into what toxcore gives them.
            not (callsNothingBack name) && any (\g -> maybe True (Set.member j) (Map.lookup g (smBytes sm)))
                (Map.findWithDefault [] name (smTargets sm))
        Nothing -> True
  where
    external name
        | Set.member name (smUnseen sm) = True
        | Platform.writesOnlyZeros name args = False
        | Just ks <- Platform.bytesWrittenThrough name = j `elem` ks
        | otherwise = True

-- | The parameter position bytes written through a kept pointer are put
-- down to.
keptParam :: Int
keptParam = -1

-- | The structs whose objects bytes may be written to.
rawStructs :: Summaries -> Set Text
rawStructs sm = Set.fromList [ st | (st, 0) <- Set.toList (smRaw sm), Map.member st (envStructs (smEnv sm)) ]

-- | The types bytes may be written to objects of: a pointer to one made a
-- pointer to something else and given where a call writes bytes through
-- it, or made one anywhere else (a @void *@ only if bytes may be written
-- through one kept), bytes taken as a pointer to one, and the structs in
-- them.
rawTypes :: Summaries -> [Function] -> Set TypeKey
rawTypes sm fns = grow (Set.fromList (concatMap own fns))
  where
    env = smEnv sm
    grow set =
        let set' = set <> Set.fromList
                [ (ctName u, 0)
                | (st, 0) <- Set.toList set
                , ft <- maybe [] Map.elems (Map.lookup st (envStructs env))
                , let u = resolveType env ft
                , ctPointers u == 0
                , Map.member (ctName u) (envStructs env) ]
        in if set' == set then set else grow set'
    own fn = go (fnBody fn)
      where
        types = fnTypes fn
        go (Fix node) = case node of
            FunctionCall (Fix (LiteralExpr C.ConstId (L _ _ m))) args
                | Just body <- expandMacro (smMacros sm) m args -> go body
            FunctionCall f args -> concat (zipWith (argument f args) [0 ..] args) ++ concatMap (go . inside) args ++ go f
            CastExpr ty x -> converted (typeOfDecl ty) x ++ go x
            VarDeclStmt (Fix (VarDecl ty _ [])) (Just e) -> converted (typeOfDecl ty) e ++ go e
            AssignExpr lhs C.AopEq rhs -> maybe [] (`converted` rhs) (typeOfExpr env types lhs) ++ go lhs ++ go rhs
            _ -> concatMap go (toList node)
        -- An argument is made its parameter's type (not for @...@); without
        -- a prototype, whatever the function takes.
        argument f args j a = case pointee =<< typeOfExpr env types (inside a) of
            Just k | isConverted, bytesThrough sm types f args j -> [k]
              where
                isConverted = case signatureOf f of
                    Just sig -> case drop j (sigParams sig) of
                        Just pt : _ -> maybe True (not . samePointer (paramType pt)) (typeOfExpr env types (inside a))
                        _           -> False
                    Nothing -> True
            _ -> []
        signatureOf f = case unFix f of
            VarExpr (L _ _ name) | Just sig <- Map.lookup name (envFunctions env) -> Just sig
            _ -> typeOfExpr env types f >>= \t -> Map.lookup (ctName (resolveType env t)) (envFunctions env)
        converted to x = case typeOfExpr env types (inside x) of
            Just from
                | Just k <- pointee from, not (samePointer to from), not (isVoid to) || smKeptWritten sm -> [k]
                | Just k <- pointee to, isBytes from -> [k]
            _ -> []
    inside x@(Fix node) = case node of
        ParenExpr y  -> inside y
        CastExpr _ y -> inside y
        _            -> x
    -- What a pointer (or an array) is to, but bytes or nothing known.
    pointee t0 =
        let t = resolveType env t0
        in if not (isPointerType t) then Nothing
           else case typeKey env (elementOf t) of
               k | k `elem` [("void", 0), ("byte", 0)] -> Nothing
                 | otherwise -> Just k
    isBytes t0 = let t = resolveType env t0 in isPointerType t && typeKey env (elementOf t) == ("byte", 0)
    isVoid t0 = let t = resolveType env t0 in ctName t == "void" && ctPointers t == 1 && null (ctDims t)
    samePointer a b = typeKey env a == typeKey env b && length (ctDims (resolveType env a)) == length (ctDims (resolveType env b))

-- | Whether a variable is a global, which every function can reach.
isGlobal :: Env -> Map Text CType -> Text -> Bool
isGlobal env types v = Map.member v (envGlobals env) && Map.lookup v types == Map.lookup v (envGlobals env)

-- | A function's C type as written, which a pointer to a function of one
-- type can only point to: its result and parameter types, without names
-- or nullability, an array parameter as the pointer it is, and a typedef
-- of an integer type as that type.
protoType :: Env -> C.Node (Lexeme Text) -> [C.Node (Lexeme Text)] -> (Text, [Text])
protoType env ret params = (written ret, mapMaybe param params)
  where
    param (Fix p) = case p of
        VarDecl ty _ dims -> Just (written ty <> T.replicate (length dims) "*")
        NonNullParam d    -> param d
        NullableParam d   -> param d
        Commented _ d     -> param d
        Ellipsis          -> Just "..."
        _                 -> Nothing
    written (Fix t) = case t of
        TyConst x               -> "(const " <> written x <> ")"
        TyPointer x             -> written x <> "*"
        TyNonnull x             -> written x
        TyNullable x            -> written x
        TyOwner x               -> written x
        TyBitwise x             -> written x
        TyForce x               -> written x
        TyStruct (L _ _ n)      -> "struct " <> n
        TyUnion (L _ _ n)       -> "union " <> n
        TyStd (L _ _ n)         -> n
        TyUserDefined (L _ _ n)
            | ct@(CType m 0 []) <- resolveType env (CType n 0 []), isJust (integerType env ct) -> m
            | otherwise -> n
        TyFunc (L _ _ n)        -> n
        _                       -> "?"

stripped :: C.Node (Lexeme Text) -> C.Node (Lexeme Text)
stripped e@(Fix node) = case node of
    ParenExpr x  -> stripped x
    CastExpr _ x -> stripped x
    _            -> e

-- | The array of a function's own nothing else can reach that an argument
-- is, or is somewhere in, given which variables something else can reach.
ownArrayIn :: Env -> Map Text CType -> (Text -> Bool) -> C.Node (Lexeme Text) -> Maybe Text
ownArrayIn env types reached a = case unFix (stripped a) of
    VarExpr (L _ _ v) | isArray v, not (reached v) -> Just v
    BinaryExpr x op _ | op `elem` [C.BopPlus, C.BopMinus] -> ownArrayIn env types reached x
    UnaryExpr C.UopAddress x
        | Just (Path v (Index{} : _)) <- pathOf x, isArray v, not (reached v) -> Just v
    _ -> Nothing
  where
    isArray v = maybe False (not . null . ctDims . resolveType env) (Map.lookup v types)

-- | Where a store to an expression is to, for what can be seen outside the
-- function: 'Nothing' for its own variables no one else can reach. Given
-- which variables something else can reach, and which of the function's
-- unchanged pointer parameters a variable is, if any.
storeLoc :: Env -> Map Text CType -> (Text -> Bool) -> (Text -> Maybe Int) -> C.Node (Lexeme Text) -> Maybe Loc
storeLoc env types reached param e@(Fix node) = case node of
    ParenExpr x -> storeLoc env types reached param x
    VarExpr (L _ _ v)
        | reached v -> LVar v . typeKey env <$> Map.lookup v types
        | otherwise -> Nothing
    MemberAccess b (L _ _ f) -> field f <$> typeOfExpr env types b <*> typeOfExpr env types e
    PointerAccess b (L _ _ f) -> field f . elementOf . resolveType env <$> typeOfExpr env types b <*> typeOfExpr env types e
    UnaryExpr C.UopDeref b -> through b
    ArrayAccess b _
        | isArray b -> storeLoc env types reached param b
        | otherwise -> through b
    _ -> Nothing
  where
    field f s t = LField (ctName (resolveType env s)) f (typeKey env t)
    isArray b = maybe False (not . null . ctDims) (resolveType env <$> typeOfExpr env types b)
    through b = case stripped b of
        Fix (VarExpr (L _ _ v)) | Just k <- param v -> Just (LParam k)
        _ -> LObject . typeKey env . elementOf . resolveType env <$> typeOfExpr env types b

-- | Where a store to an expression in a function is to, as effects:
-- 'Nothing' for the function's own variables, and where it can't be told.
storeAt :: Summaries -> Map Text CType -> (Text -> Bool) -> C.Node (Lexeme Text) -> Maybe Effects
storeAt sm types reached = fmap (single sm) . storeLoc (smEnv sm) types reached (const Nothing)

-- | The places a place is in, for what may change it: the fields and
-- objects on the way to it, and the variable it starts from if anything
-- else can reach it. An array is where it is: storing to its elements
-- changes only what's in it, so it's in nothing but what it's part of.
-- Where a type on the way isn't known, it may be anywhere.
footprint :: Env -> Map Text CType -> (Text -> Bool) -> Path -> [Loc]
footprint env types reached (Path root steps) = rootLocs ++ go rootType steps
  where
    rootType = Map.lookup root types
    rootLocs
        | null steps && maybe False isArray rootType = []
        | not (reached root) = [ LOwn root | maybe False isArray rootType ]
        | otherwise = maybe [LSomewhere] (\t -> [LVar root (typeKey env t)]) rootType
    isArray = not . null . ctDims . resolveType env
    go _ [] = []
    go Nothing _ = [LSomewhere]
    go (Just t0) (step : rest) =
        let t = resolveType env t0
        in case step of
            Field f -> case Map.lookup (ctName t) (envStructs env) >>= Map.lookup f of
                Just ft
                    | null rest && isArray ft -> []
                    | otherwise -> LField (ctName t) f (typeKey env ft) : go (Just ft) rest
                Nothing -> [LSomewhere]
            Index _ _ | not (null (ctDims t)) -> go (Just t { ctDims = drop 1 (ctDims t) }) rest
            _ -> let e = elementOf t in LObject (typeKey env e) : go (Just e) rest

-- | What a pointer points to, or an array's element.
elementOf :: CType -> CType
elementOf t = case ctDims t of
    _ : ds -> t { ctDims = ds }
    []     -> t { ctPointers = max 0 (ctPointers t - 1) }

-- | Where a call may store. Given which variables something else can reach
-- and which of the calling function's unchanged pointer parameters a
-- variable is, to say what the callee's stores through its parameters are
-- to.
callEffects :: Summaries -> Map Text CType -> (Text -> Bool) -> (Text -> Maybe Int) -> C.Node (Lexeme Text) -> [C.Node (Lexeme Text)] -> Effects
callEffects sm types reached param f args = case f of
    Fix (VarExpr (L _ _ name))
        | not (Map.member name types), Just e <- Map.lookup name (smFunctions sm) -> given e
        | not (Map.member name types) -> external name
    Fix (LiteralExpr C.ConstId (L _ _ name))
        | Just body <- expandMacro (smMacros sm) name args ->
            foldMap here (subnodes body)
        | otherwise -> mempty
    _ -> throughPointer
  where
    env = smEnv sm
    here (Fix node) = case node of
        AssignExpr lhs _ _ -> stored lhs
        UnaryExpr o x | o `elem` [C.UopIncr, C.UopDecr] -> stored x
        FunctionCall g as -> callEffects sm types reached param g as
        _ -> mempty
    stored x = maybe mempty (single sm) (storeLoc env types reached param x)
    -- The callee's stores through its parameters are to what it's given
    -- there.
    given = \case
        Anything -> Anything
        Only st -> Only st { stParams = Set.empty } <> foldMap through (Set.toList (stParams st))
    through k = case drop k args of
        arg : _ -> pointee arg
        []      -> Anything
    -- What a store through an argument may be to: an array of the caller's
    -- own, the place whose address it is, an array (a field's is that
    -- field: more is reported), the caller's own parameter, or an object of
    -- the type it points to.
    pointee arg | Just v <- ownArrayIn env types reached arg = single sm (LOwn v)
    pointee arg = case stripped arg of
        Fix (UnaryExpr C.UopAddress x) -> stored x
        x@(Fix MemberAccess{}) | fieldArray x -> stored x
        x@(Fix PointerAccess{}) | fieldArray x -> stored x
        Fix (VarExpr (L _ _ v))
            | Just k <- param v -> single sm (LParam k)
            | isArray v -> stored (stripped arg)
        _ -> case resolveType env <$> typeOfExpr env types arg of
            Just t | isPointerType t ->
                let t' = elementOf t
                in single sm (LObject (typeKey env t'))
            _ -> mempty
    isArray v = maybe False (not . null . ctDims . resolveType env) (Map.lookup v types)
    fieldArray x = maybe False (not . null . ctDims . resolveType env) (typeOfExpr env types x)
    -- A library's function stores only through the pointers it's given,
    -- or those of them it's known to write through, and calls the
    -- functions it's given.
    external name
        | Set.member name (smUnseen sm) = Anything
        | Platform.storesNothing name = mempty
        | Just ks <- Platform.bytesWrittenThrough name = foldMap argument [ a | (j, a) <- zip [0 ..] args, j `elem` ks ]
        | otherwise = foldMap argument args
    argument a = case stripped a of
        Fix (VarExpr (L _ _ g)) | not (Map.member g types), Just e <- Map.lookup g (smFunctions sm) -> e
        _ -> pointee a
    throughPointer = case typeOfExpr env types f of
        Just t | name <- ctName (resolveType env t) ->
            if callsNothingBack name then mempty
            else case Map.findWithDefault [] name (smTargets sm) of
                []      -> Anything
                targets -> foldMap (\g -> given (fromMaybe Anything (Map.lookup g (smFunctions sm)))) targets
        Nothing -> Anything

-- | The program's functions given as a function type: what a call through
-- a pointer of the type may call.
targetsOf :: Summaries -> Text -> [Text]
targetsOf sm name = Map.findWithDefault [] name (smTargets sm)

-- | Callbacks the API says may not call back into toxcore, which so change
-- nothing of its: the log callback may be called in the middle of any
-- function.
callsNothingBack :: Text -> Bool
callsNothingBack = (== "tox_log_cb")
