{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Standard.Base (typeCheckProgram, TypeCheckState(..), checkStmt, checkFunctionDefn, collectDefinitions, inferExpr, reportError, lookupMember, checkExprWithExpected) where

import           Control.Applicative                          ((<|>))
import           Control.Arrow                                (second)
import           Control.Monad                                (foldM, forM_,
                                                               join)
import           Control.Monad.State.Strict                   (State, StateT,
                                                               lift)
import qualified Control.Monad.State.Strict                   as State
import           Data.Fix                                     (Fix (..),
                                                               foldFix, unFix)
import qualified Data.Graph                                   as Graph
import           Data.List                                    (find)
import           Data.Map.Strict                              (Map)
import qualified Data.Map.Strict                              as Map
import           Data.Maybe                                   (catMaybes,
                                                               fromMaybe,
                                                               isJust, mapMaybe)
import           Data.Set                                     (Set)
import qualified Data.Set                                     as Set
import           Data.Text                                    (Text)
import qualified Data.Text                                    as T
import qualified Data.Text                                    as Text
import qualified Debug.Trace                                  as Debug
import           Language.Cimple                              (Lexeme (..),
                                                               Node, NodeF (..))
import qualified Language.Cimple                              as C
import qualified Language.Cimple.Program                      as Program
import           Language.Hic.Core.AstUtils                   (getLexeme,
                                                               isLvalue)
import           Language.Hic.Core.Errors
import           Language.Hic.Core.Pretty                     (explainType,
                                                               ppErrorInfo,
                                                               showType)
import           Language.Hic.Core.TypeSystem                 (FullTemplate,
                                                               FullTemplateF (..),
                                                               Invariant (..),
                                                               Phase (..),
                                                               StdType (..),
                                                               TemplateId (..),
                                                               TypeDescr (..),
                                                               TypeInfo,
                                                               TypeInfoF (..),
                                                               TypeRef (..),
                                                               TypeSystem,
                                                               isVoid,
                                                               pattern Array,
                                                               pattern BuiltinType,
                                                               pattern Conflict,
                                                               pattern Const,
                                                               pattern EnumMem,
                                                               pattern ExternalType,
                                                               pattern FullTemplate,
                                                               pattern Function,
                                                               pattern IntLit,
                                                               pattern NameLit,
                                                               pattern Nonnull,
                                                               pattern Nullable,
                                                               pattern Owner,
                                                               pattern Pointer,
                                                               pattern Proxy,
                                                               pattern Qualified,
                                                               pattern Singleton,
                                                               pattern Sized,
                                                               pattern Template,
                                                               pattern TypeRef,
                                                               pattern Unconstrained,
                                                               pattern Var,
                                                               pattern VarArg,
                                                               templateIdBaseName,
                                                               templateIdToText)
import           Language.Hic.TypeSystem.Core.Base            (builtin,
                                                               containsTemplate,
                                                               getInnerType,
                                                               getTypeLexeme,
                                                               isAnyStruct,
                                                               isInt, isLPSTR,
                                                               isNetworkingStruct,
                                                               isPointerLike,
                                                               isPointerToChar,
                                                               isSockaddr,
                                                               isSpecial,
                                                               lookupType,
                                                               promote, unwrap)
import qualified Language.Hic.TypeSystem.Core.Base            as TS
import qualified Language.Hic.TypeSystem.Core.Base            as TypeSystem
import           Language.Hic.TypeSystem.Core.BuiltinMap      (builtinMap)
import           Language.Hic.TypeSystem.Standard.Constraints (extractConstraints)
import           Language.Hic.TypeSystem.Standard.Solver      (solveConstraints)
import           Prettyprinter                                (Doc,
                                                               defaultLayoutOptions,
                                                               layoutPretty,
                                                               unAnnotate)
import           Prettyprinter.Render.Terminal                (AnsiStyle,
                                                               renderStrict)

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

-- | Type checking state
data TypeCheckState = TypeCheckState
    { tcsTypeSystem :: TypeSystem
    , tcsVars       :: Map Text (TypeInfo 'Local, Provenance 'Local)
    , tcsMacros     :: Map Text ([Text], Node (Lexeme Text))
    , tcsBounds     :: Map (FullTemplate 'Local) (TypeInfo 'Local, Provenance 'Local)
    , tcsNextId     :: Int
    , tcsErrors     :: [ErrorInfo 'Local]
    , tcsReturnType :: Maybe (TypeInfo 'Local)
    , tcsGlobals    :: Set Text
    , tcsContext    :: [Context 'Local]
    }

type TypeCheck = State TypeCheckState

-- | Push a context onto the stack
pushContext :: Context 'Local -> TypeCheck ()
pushContext c = State.modify $ \s -> s { tcsContext = c : tcsContext s }

-- | Pop a context from the stack
popContext :: TypeCheck ()
popContext = State.modify $ \s -> s { tcsContext = drop 1 (tcsContext s) }

-- | Execute an action within a context
withContext :: Context 'Local -> TypeCheck a -> TypeCheck a
withContext c m = do
    pushContext c
    res <- m
    popContext
    return res

-- | Execute an action within an expression context
atExpr :: Node (Lexeme Text) -> TypeCheck a -> TypeCheck a
atExpr = withContext . InExpr

-- | Execute an action within a statement context
atStmt :: Node (Lexeme Text) -> TypeCheck a -> TypeCheck a
atStmt = withContext . InStmt

-- | Report a structured error
reportTypeError :: TypeError 'Local -> TypeCheck ()
reportTypeError err = do
    ctx <- State.gets tcsContext
    bounds <- State.gets tcsBounds
    let loc = findLoc ctx
    (err', expls) <- case err of
        TypeMismatch exp' act reason mDetail -> do
            eResolved <- resolveType =<< applyBindings exp'
            aResolved <- resolveType =<< applyBindings act
            let expls = explainType bounds exp' ++ explainType bounds act
            return (TypeMismatch eResolved aResolved reason mDetail, expls)
        _ -> return (err, [])
    State.modify $ \s -> s { tcsErrors = tcsErrors s ++ [ErrorInfo loc ctx err' expls] }
  where
    findLoc []                    = Nothing
    findLoc (InExpr n : _)        = getLexeme n
    findLoc (InStmt n : _)        = getLexeme n
    findLoc (InInitializer n : _) = getLexeme n
    findLoc (_ : cs)              = findLoc cs

-- | Report an error (legacy)
reportError :: Maybe (Lexeme Text) -> Text -> TypeCheck ()
reportError l msg = do
    ctx <- State.gets tcsContext
    State.modify $ \s -> s { tcsErrors = tcsErrors s ++ [ErrorInfo l ctx (CustomError msg) []] }

nextTemplate :: Maybe Text -> TypeCheck (TypeInfo 'Local)
nextTemplate mHint = do
    i <- State.gets tcsNextId
    State.modify $ \s -> s { tcsNextId = i + 1 }
    return $ Template (TIdSolver i mHint) Nothing

getCallable :: TypeInfo 'Local -> TypeCheck (Maybe (TypeInfo 'Local, [TypeInfo 'Local]))
getCallable ty = do
    rt <- resolveType ty
    case unwrap rt of
        Function ret params -> return $ Just (ret, params)
        Pointer p -> getCallable p
        TypeRef FuncRef (L _ _ tid) args -> do
            let name = templateIdBaseName tid
            ts <- State.gets tcsTypeSystem
            case lookupType name ts of
                Just descr -> do
                    dtraceM $ "getCallable expanding " ++ Text.unpack name ++ " with args " ++ show args
                    case TypeSystem.instantiateDescr 0 TS.TopLevel (Map.fromList (zip (TypeSystem.getDescrTemplates descr) args)) descr of
                        FuncDescr _ _ ret params -> return $ Just (ret, params)
                        _                        -> return Nothing
                Nothing -> return Nothing
        _ -> return Nothing

resolveType :: TypeInfo 'Local -> TypeCheck (TypeInfo 'Local)
resolveType ty = case unFix ty of
    PointerF t -> Pointer <$> resolveType t
    QualifiedF qs t -> Qualified qs <$> resolveType t
    SizedF t l -> flip Sized l <$> resolveType t
    _ -> do
        ts <- State.gets tcsTypeSystem
        bounds <- State.gets tcsBounds
        let initialKey = toKey ty
            reachableKeys = collectReachable ts bounds Set.empty [initialKey]
            nodes = [ (k, k, getDeps ts bounds k) | k <- Set.toList reachableKeys ]
            sccs = Graph.stronglyConnComp nodes
            resolvedMap = foldl (resolveScc ts bounds) Map.empty sccs
        return $ fromMaybe ty (Map.lookup initialKey resolvedMap)
  where
    toKey (Fix (VarF _ inner)) = toKey inner
    toKey t@(Fix (TypeRefF _ (L _ _ tid) _)) = (Left (templateIdBaseName tid), Just t)
    toKey t@(Fix (TemplateF ft)) = (Right ft, Just t)
    toKey t = (Left "", Just t)

    getDeps ts bounds = \case
        (Left name, _) ->
            if name == "" then []
            else case lookupType name ts of
                Just (AliasDescr _ _ target) -> [toKey (TS.toLocal 0 TS.TopLevel target)]
                _                            -> []
        (Right key, _) ->
            case Map.lookup key bounds of
                Just (target, _) -> [toKey target]
                _                -> []

    collectReachable _ _ seen [] = seen
    collectReachable ts bounds seen (k:ks)
        | Set.member k seen = collectReachable ts bounds seen ks
        | otherwise = collectReachable ts bounds (Set.insert k seen) (getDeps ts bounds k ++ ks)

    resolveScc ts bounds acc (Graph.AcyclicSCC k@(key, mTy)) =
        case key of
            Left name ->
                if name == "" then Map.insert k (fromMaybe (TS.Unsupported "empty") mTy) acc
                else case lookupType name ts of
                    Just (AliasDescr _ _ target) -> Map.insert k (fromMaybe (TS.toLocal 0 TS.TopLevel target) (Map.lookup (toKey (TS.toLocal 0 TS.TopLevel target)) acc)) acc
                    Just (StructDescr ld _ _ _) -> Map.insert k (fromMaybe (TypeRef StructRef (fmap (const (TIdAnonymous 0 (Just (C.lexemeText ld)))) ld) []) mTy) acc
                    Just (UnionDescr ld _ _ _)  -> Map.insert k (fromMaybe (TypeRef UnionRef (fmap (const (TIdAnonymous 0 (Just (C.lexemeText ld)))) ld) []) mTy) acc
                    Just (EnumDescr ld _)     -> Map.insert k (fromMaybe (TypeRef EnumRef (fmap (const (TIdAnonymous 0 (Just (C.lexemeText ld)))) ld) []) mTy) acc
                    Just (IntDescr ld _)      -> Map.insert k (fromMaybe (TypeRef IntRef (fmap (const (TIdAnonymous 0 (Just (C.lexemeText ld)))) ld) []) mTy) acc
                    Just (FuncDescr _ _ ret params) -> Map.insert k (Function (TS.toLocal 0 TS.TopLevel ret) (map (TS.toLocal 0 TS.TopLevel) params)) acc
                    _ -> Map.insert k (fromMaybe (TS.Unsupported "unknown") mTy) acc
            Right k' ->
                case Map.lookup k' bounds of
                    Just (target, _) -> Map.insert k (fromMaybe target (Map.lookup (toKey target) acc)) acc
                    _ -> Map.insert k (fromMaybe (TS.Unsupported "unknown template") mTy) acc

    resolveScc _ _ acc (Graph.CyclicSCC ks) =
        foldl (\m k@(_, mTy) -> Map.insert k (fromMaybe (TS.Unsupported "cycle") mTy) m) acc ks



insertType :: Lexeme Text -> TypeDescr 'Global -> TypeCheck ()
insertType name ty = do
    let nameText = C.lexemeText name
    existing <- State.gets (Map.lookup nameText . tcsTypeSystem)
    case (ty, existing) of
        -- If we have a typedef that points to a struct/union/enum of the same name,
        -- and we already have the definition, ignore the typedef.
        (AliasDescr _ _ (TypeRef _ (L _ _ tid) _), Just StructDescr{}) | templateIdBaseName tid == nameText ->
            return ()
        (AliasDescr _ _ (TypeRef _ (L _ _ tid) _), Just UnionDescr{})  | templateIdBaseName tid == nameText ->
            return ()
        (AliasDescr _ _ (TypeRef _ (L _ _ tid) _), Just EnumDescr{})   | templateIdBaseName tid == nameText ->
            return ()

        -- If we are adding a definition and we have a typedef of the same name
        -- that points to this name, overwrite it.
        (StructDescr{}, Just (AliasDescr _ _ (TypeRef _ (L _ _ tid) _))) | templateIdBaseName tid == nameText ->
            State.modify $ \s -> s { tcsTypeSystem = Map.insert nameText ty (tcsTypeSystem s) }
        (UnionDescr{}, Just (AliasDescr _ _ (TypeRef _ (L _ _ tid) _)))  | templateIdBaseName tid == nameText ->
            State.modify $ \s -> s { tcsTypeSystem = Map.insert nameText ty (tcsTypeSystem s) }

        -- Merge struct/union definitions, keeping the one with members.
        (StructDescr _ _ mems _, Just (StructDescr _ _ existingMems _)) ->
            if not (null mems) || null existingMems
                then State.modify $ \s -> s { tcsTypeSystem = Map.insert nameText ty (tcsTypeSystem s) }
                else return ()
        (UnionDescr _ _ mems _, Just (UnionDescr _ _ existingMems _)) ->
            if not (null mems) || null existingMems
                then State.modify $ \s -> s { tcsTypeSystem = Map.insert nameText ty (tcsTypeSystem s) }
                else return ()

        -- Otherwise, just overwrite. Pass 1 information is generally better.
        _ ->
            State.modify $ \s -> s { tcsTypeSystem = Map.insert nameText ty (tcsTypeSystem s) }


-- | Infer the type of an expression
inferExpr :: Node (Lexeme Text) -> TypeCheck (TypeInfo 'Local)
inferExpr (Fix node) = atExpr (Fix node) $ do
    case node of
        -- Literals
        LiteralExpr C.Int _    -> return $ BuiltinType S32Ty
        LiteralExpr C.Char _   -> return $ BuiltinType CharTy
        LiteralExpr C.Bool _   -> return $ BuiltinType BoolTy
        LiteralExpr C.String _ -> return $ Pointer (BuiltinType CharTy)
        LiteralExpr C.ConstId (L _ _ name) -> do
            if name == "nullptr"
                then return $ BuiltinType NullPtrTy
                else if name == "__FILE__" || name == "__func__"
                then return $ Pointer (Const (BuiltinType CharTy))
                else if name == "__LINE__"
                then return $ BuiltinType S32Ty
                else do
                    vars <- State.gets tcsVars
                    case Map.lookup name vars of
                        Just (ty, _) -> return ty
                        Nothing -> do
                            macros <- State.gets tcsMacros
                            case Map.lookup name macros of
                                Just ([], body) -> inferExpr body
                                _               -> return $ BuiltinType S32Ty

        -- Variables
        VarExpr (L _ _ name) -> do
            vars <- State.gets tcsVars
            case Map.lookup name vars of
                Just (ty, _) -> return ty
                Nothing -> do
                    macros <- State.gets tcsMacros
                    case Map.lookup name macros of
                        Just ([], body) -> inferExpr body
                        _ -> do
                            reportTypeError $ UndefinedVariable name
                            return $ BuiltinType VoidTy

        -- Unary Operators
        UnaryExpr op expr -> do
            case op of
                C.UopIncr -> checkLvalue expr
                C.UopDecr -> checkLvalue expr
                _         -> return ()
            t <- inferExpr expr
            case op of
                C.UopDeref -> do
                    rt <- resolveType t
                    if isPointerLike rt
                        then return $ getInnerType rt
                        else do
                            reportTypeError $ DereferencingNonPointer rt
                            return t
                C.UopAddress -> return $ Pointer t
                _ -> return t
          where
            checkLvalue e =
                if not (isLvalue e)
                then reportTypeError NotALValue
                else return ()

        -- Binary Operators
        BinaryExpr lhs op rhs -> do
            lt <- inferExpr lhs
            rt <- inferExpr rhs
            case op of
                C.BopEq  -> unify lt rt GeneralMismatch (getLexeme lhs) >> return (BuiltinType BoolTy)
                C.BopNe  -> unify lt rt GeneralMismatch (getLexeme lhs) >> return (BuiltinType BoolTy)
                C.BopLt  -> unify lt rt GeneralMismatch (getLexeme lhs) >> return (BuiltinType BoolTy)
                C.BopLe  -> unify lt rt GeneralMismatch (getLexeme lhs) >> return (BuiltinType BoolTy)
                C.BopGt  -> unify lt rt GeneralMismatch (getLexeme lhs) >> return (BuiltinType BoolTy)
                C.BopGe  -> unify lt rt GeneralMismatch (getLexeme lhs) >> return (BuiltinType BoolTy)
                C.BopAnd -> do
                    checkExprWithExpected (BuiltinType BoolTy) lhs
                    checkExprWithExpected (BuiltinType BoolTy) rhs
                    return $ BuiltinType BoolTy
                C.BopOr  -> do
                    checkExprWithExpected (BuiltinType BoolTy) lhs
                    checkExprWithExpected (BuiltinType BoolTy) rhs
                    return $ BuiltinType BoolTy
                C.BopPlus -> do
                    if isPointerLike lt
                        then do
                            checkExprWithExpected (BuiltinType S32Ty) rhs
                            return lt
                        else if isPointerLike rt
                        then do
                            checkExprWithExpected (BuiltinType S32Ty) lhs
                            return rt
                        else do
                            unify lt rt GeneralMismatch (getLexeme lhs)
                            return $ promote lt rt
                C.BopMinus -> do
                    if isPointerLike lt && isPointerLike rt
                        then return $ BuiltinType SizeTy
                        else if isPointerLike lt
                        then do
                            checkExprWithExpected (BuiltinType S32Ty) rhs
                            return lt
                        else do
                            unify lt rt GeneralMismatch (getLexeme lhs)
                            return $ promote lt rt
                _ -> do
                    unify lt rt GeneralMismatch (getLexeme lhs)
                    return $ promote lt rt

        -- Function Calls & Macro Instantiation
        FunctionCall fun args -> do
            case fun of
                Fix (VarExpr (L _ _ name)) -> macroOrFunc name fun args
                Fix (LiteralExpr C.ConstId (L _ _ name)) -> macroOrFunc name fun args
                Fix (LiteralExpr C.String (L _ _ name)) -> macroOrFunc name fun args
                _ -> do
                    ft <- inferExpr fun
                    mc <- getCallable ft
                    dtraceM $ "getCallable: ft=" ++ show ft ++ " mc=" ++ show mc
                    case mc of
                        Just (ret, params) -> do
                            checkArgs params args
                            return ret
                        Nothing -> return $ BuiltinType VoidTy

        -- Member Access
        MemberAccess base l@(L _ _ _) -> do
            bt <- inferExpr base
            lookupMember bt l

        PointerAccess base l@(L _ _ _) -> do
            bt <- inferExpr base
            rt <- resolveType bt
            case unwrap rt of
                Pointer inner -> lookupMember inner l
                _ -> do
                    reportTypeError $ DereferencingNonPointer rt
                    return $ BuiltinType VoidTy

        -- Array Access
        ArrayAccess base _ -> do
            bt <- inferExpr base
            rt <- resolveType bt
            case unwrap rt of
                Pointer inner -> return inner
                Array (Just inner) _ -> return inner
                Array Nothing (inner:_) -> return inner
                _ -> do
                    reportTypeError $ ArrayAccessNonArray rt
                    return $ BuiltinType VoidTy

        -- Parentheses
        ParenExpr expr -> inferExpr expr

        -- Casts
        CastExpr ty expr -> do
            t <- convertToTypeInfo ty
            at <- inferExpr expr
            unify t at GeneralMismatch (getLexeme expr)
            return t

        -- Compound Literal
        CompoundLiteral ty expr -> do
            t <- convertToTypeInfo ty
            at <- inferExpr expr
            unify t at GeneralMismatch (getLexeme expr)
            return t

        -- Sizeof
        SizeofExpr _ -> return $ BuiltinType SizeTy
        SizeofType _ -> return $ BuiltinType SizeTy

        -- Initialiser List
        InitialiserList exprs -> do
            tys <- mapM inferExpr exprs
            case tys of
                []    -> return $ Array Nothing []
                (t:_) -> return $ Array (Just t) tys

        -- Assignment
        AssignExpr lhs _ rhs -> do
            if not (isLvalue lhs)
                then reportTypeError NotALValue
                else return ()
            lt <- inferExpr lhs
            rt <- inferExpr rhs
            unify lt rt AssignmentMismatch (getLexeme lhs)
            return lt

        -- Ternary operator
        TernaryExpr cond thenExpr elseExpr -> do
            checkExprWithExpected (BuiltinType BoolTy) cond
            tt <- inferExpr thenExpr
            et <- inferExpr elseExpr
            unify tt et GeneralMismatch (getLexeme thenExpr)
            return $ promote tt et

        _ -> return $ BuiltinType VoidTy


-- | Helper for FunctionCall to handle both macros and functions
macroOrFunc :: Text -> Node (Lexeme Text) -> [Node (Lexeme Text)] -> TypeCheck (TypeInfo 'Local)
macroOrFunc name fun args = do
    macros <- State.gets tcsMacros
    case Map.lookup name macros of
        Just (params, body) -> do
            dtraceM $ "instantiateMacro call: " ++ Text.unpack name
            instantiateMacro name params args body
        Nothing -> do
            ft <- inferExpr fun
            mc <- getCallable ft
            case mc of
                Just (ret, params) -> do
                    -- Refresh templates only for global functions to allow polymorphism.
                    -- Local variables (like callback parameters) should not be refreshed
                    -- because their templates represent specific (though inferred) types
                    -- that should be consistent across calls in the same scope.
                    globals <- State.gets tcsGlobals
                    isGlobal <- case fun of
                        Fix (VarExpr (L _ _ name')) -> return $ Set.member name' globals
                        _                           -> return False

                    ft'' <- if isGlobal
                                then refreshTemplates (Function ret params)
                                else return (Function ret params)
                    case ft'' of
                        Function ret' params' -> do
                            checkArgs params' args
                            return ret'
                        _ -> error "impossible"
                Nothing -> do
                    let name' = case getTypeLexeme ft of
                            Just (L _ _ t) -> t
                            Nothing        -> name
                    reportTypeError $ CallingNonFunction name' ft
                    return $ BuiltinType VoidTy

checkArgs :: [TypeInfo 'Local] -> [Node (Lexeme Text)] -> TypeCheck ()
checkArgs params args = do
    let expected = length (filter (not . isSpecial) params)
    let actual = length args
    let isVariadic = VarArg `elem` params
    if actual < expected
        then reportTypeError $ TooFewArgs expected actual
        else if actual > expected && not isVariadic
            then reportTypeError $ TooManyArgs expected actual
            else go params args
  where
    go (VarArg : _) _ = return ()
    go _ (Fix (VarExpr (L _ _ "__VA_ARGS__")) : _) = return ()
    go _ (Fix (LiteralExpr C.ConstId (L _ _ "__VA_ARGS__")) : _) = return ()
    go (BuiltinType VoidTy : ps) as = go ps as
    go (p : ps) (a : as) = do
        checkExprWithExpected p a
        go ps as
    go _ _ = return ()


-- | Type check a whole program
typeCheckProgram :: Program.Program Text -> [(FilePath, ErrorInfo 'Local)]
typeCheckProgram program =
    let programList = Program.toList program
        ts = TypeSystem.collect programList
        -- Extract constraints from all files, threading the counters
        (allConstraints, extractionErrors, _, _) = foldl (\(accCs, accErrs, nextId, nextCallSiteId) (path, nodes) ->
                                        let (cs, errs, nextId', nextCallSiteId') = extractConstraints ts path (Fix (C.Group nodes)) nextId nextCallSiteId
                                        in (accCs ++ cs, accErrs ++ errs, nextId', nextCallSiteId')) ([], [], 0, 0) programList
        -- Solve them all together
        solveErrors = solveConstraints ts allConstraints

        allErrors = extractionErrors ++ solveErrors

        extractPath ei = case find isFile (errContext ei) of
            Just (InFile p) -> p
            _               -> "unknown"
          where
            isFile = \case InFile _ -> True; _ -> False

    in map (\ei -> (extractPath ei, ei)) allErrors


-- | Look up a member in a struct or union
lookupMember :: TypeInfo 'Local -> Lexeme Text -> TypeCheck (TypeInfo 'Local)
lookupMember ty l@(L _ _ field) = withContext (InMemberAccess field) $ do
    ts <- State.gets tcsTypeSystem
    rt <- resolveType ty
    case rt of
        TypeRef _ (L _ _ tid) args ->
            let name = templateIdBaseName tid in
            case lookupType name ts of
                Just descr -> do
                    let instantiated = instantiateDescr descr args
                    case TS.lookupMemberType field instantiated of
                        Just mt -> return mt
                        Nothing -> do
                            reportTypeError $ MemberNotFound field rt
                            return $ BuiltinType VoidTy
                Nothing -> do
                    reportTypeError $ UndefinedType name
                    return $ BuiltinType VoidTy
        Const t -> lookupMember t l
        Owner t -> lookupMember t l
        Nonnull t -> lookupMember t l
        Nullable t -> lookupMember t l
        Sized t _ -> lookupMember t l
        _ -> do
            reportTypeError $ NotAStruct rt
            return $ BuiltinType VoidTy

instantiateDescr :: TypeDescr 'Global -> [TypeInfo 'Local] -> TypeDescr 'Local
instantiateDescr descr args =
    case descr of
        StructDescr l tps mems invs ->
            let m = Map.fromList (zip tps args)
            in StructDescr l [] (map (second (instantiate m)) mems) (map (instantiateInvariant m) invs)
        UnionDescr l tps mems invs ->
            let m = Map.fromList (zip tps args)
            in UnionDescr l [] (map (second (instantiate m)) mems) (map (instantiateInvariant m) invs)
        FuncDescr l tps ret ps ->
            let m = Map.fromList (zip tps args)
            in dtrace ("instantiateDescr: m=" ++ show m ++ " ps=" ++ show ps) $
               FuncDescr l [] (instantiate m ret) (map (instantiate m) ps)
        AliasDescr l tps ty ->
            let m = Map.fromList (zip tps args)
            in AliasDescr l [] (instantiate m ty)
        t -> TS.instantiateDescr 0 TS.TopLevel Map.empty t
  where
    instantiateInvariant m = \case
        InvCallable f as r -> InvCallable (instantiate m f) (map (instantiate m) as) (instantiate m r)
        InvEquality t1 t2  -> InvEquality (instantiate m t1) (instantiate m t2)
        InvSubtype t1 t2   -> InvSubtype (instantiate m t1) (instantiate m t2)
        InvCoordinatedPair t1 t2 t3 -> InvCoordinatedPair (instantiate m t1) (instantiate m t2) (instantiate m t3)

    instantiate m = \case
        Template t i ->
            case Map.lookup t m of
                Just res -> res
                Nothing  -> Template (TIdAnonymous 0 (TS.templateIdHint t)) (fmap (instantiate m) i)
        Pointer t -> Pointer (instantiate m t)
        Array mt dims -> Array (fmap (instantiate m) mt) (map (instantiate m) dims)
        Function r ps -> Function (instantiate m r) (map (instantiate m) ps)
        TypeRef ref l args' -> TypeRef ref (fmap convert l) (map (instantiate m) args')
        Const t -> Const (instantiate m t)
        Owner t -> Owner (instantiate m t)
        Nonnull t -> Nonnull (instantiate m t)
        Nullable t -> Nullable (instantiate m t)
        Qualified qs t -> Qualified qs (instantiate m t)
        Sized t l -> Sized (instantiate m t) (fmap convert l)
        Var l t -> Var (fmap convert l) (instantiate m t)
        BuiltinType s -> BuiltinType s
        ExternalType l -> ExternalType (fmap convert l)
        Singleton s i' -> Singleton s i'
        VarArg -> VarArg
        IntLit l -> IntLit (fmap convert l)
        NameLit l -> NameLit (fmap convert l)
        EnumMem l -> EnumMem (fmap convert l)
        Unconstrained -> Unconstrained
        Conflict -> Conflict
        Proxy t -> Proxy (instantiate m t)
        TS.Unsupported msg -> TS.Unsupported msg

    convert :: TemplateId 'Global -> TemplateId 'Local
    convert (TIdName n)        = TIdAnonymous 0 (Just n)
    convert (TIdParam _ h _)   = TIdAnonymous 0 h
    convert (TIdAnonymous _ h) = TIdAnonymous 0 h
    convert (TIdRec i)         = TIdRec i


-- | Instantiate a macro "template"
instantiateMacro :: Text -> [Text] -> [Node (Lexeme Text)] -> Node (Lexeme Text) -> TypeCheck (TypeInfo 'Local)
instantiateMacro name params args body = withContext (InMacro name) $ do
    if length params > length args
        then do
            reportTypeError $ MacroArgumentMismatch name (length params) (length args)
            return $ BuiltinType VoidTy
        else do
            -- Infer types of arguments
            argTypes <- mapM inferExpr args
            -- Save current variable environment
            oldVars <- State.gets tcsVars
            -- Bind parameters to argument types
            let bindings = Map.fromList [ (p, (t, FromInference body)) | (p, t) <- zip params argTypes ]
            -- Handle variadic macros by binding __VA_ARGS__ to the remaining arguments
            let vaArgs = drop (length params) args
            let bindings' = case vaArgs of
                                [] -> bindings
                                _  -> Map.insert "__VA_ARGS__" (Array Nothing [], FromInference body) bindings -- Special handling for __VA_ARGS__ expansion
            dtraceM $ "instantiateMacro: " ++ Text.unpack name ++ " bindings=" ++ show bindings'
            State.modify $ \s -> s { tcsVars = Map.union bindings' (tcsVars s) }
            -- Type-check the body with these bindings
            dtraceM ("instantiateMacro: " ++ Text.unpack name ++ " body node type=" ++ show (fmap (const ()) (unFix body)))
            res <- case body of
                Fix (MacroBodyStmt stmt) -> do
                    dtraceM ("instantiateMacro: Branch MacroBodyStmt")
                    checkStmt stmt
                    return $ BuiltinType VoidTy
                Fix (MacroBodyFunCall expr) -> do
                    dtraceM ("instantiateMacro: Branch MacroBodyFunCall")
                    inferExpr expr
                _ -> do
                    dtraceM ("instantiateMacro: Branch other")
                    inferExpr body
            -- Restore environment
            State.modify $ \s -> s { tcsVars = oldVars }
            return res


-- | Convert an AST node representing a type to TypeInfo
convertToTypeInfo :: Node (Lexeme Text) -> TypeCheck (TypeInfo 'Local)
convertToTypeInfo (Fix node) = case node of
    TyStd l                -> return $ TS.toLocal 0 TS.TopLevel (TS.builtin l)
    TyPointer t            -> Pointer <$> (convertToTypeInfo t >>= replaceVoidWithTemplate)
    TyConst t              -> Const <$> convertToTypeInfo t
    TyOwner t              -> Owner <$> convertToTypeInfo t
    TyNonnull t            -> Nonnull <$> convertToTypeInfo t
    TyNullable t           -> Nullable <$> convertToTypeInfo t
    TyStruct l@(L _ _ name) -> do
        ts <- State.gets tcsTypeSystem
        case lookupType name ts of
            Just descr -> do
                let tps = TypeSystem.getDescrTemplates descr
                args <- mapM (nextTemplate . TS.templateIdHint) tps
                return $ TypeRef StructRef (fmap TS.mkId l) args
            Nothing -> return $ TypeRef UnresolvedRef (fmap TS.mkId l) []
    TyUnion l@(L _ _ name)  -> do
        ts <- State.gets tcsTypeSystem
        case lookupType name ts of
            Just descr -> do
                let tps = TypeSystem.getDescrTemplates descr
                args <- mapM (nextTemplate . TS.templateIdHint) tps
                return $ TypeRef UnionRef (fmap TS.mkId l) args
            Nothing -> return $ TypeRef UnresolvedRef (fmap TS.mkId l) []
    TyFunc l@(L _ _ name) -> do
        ts <- State.gets tcsTypeSystem
        case lookupType name ts of
            Just descr -> do
                let tps = TypeSystem.getDescrTemplates descr
                dtraceM $ "convertToTypeInfo TyFunc: " ++ Text.unpack name ++ " tps=" ++ show tps
                args <- mapM (nextTemplate . TS.templateIdHint) tps
                return $ TypeRef FuncRef (fmap TS.mkId l) args
            Nothing -> return $ TypeRef UnresolvedRef (fmap TS.mkId l) []
    TyUserDefined (L pos ty name) -> do
        ts <- State.gets tcsTypeSystem
        case lookupType name ts of
            Just descr -> do
                let tps = TypeSystem.getDescrTemplates descr
                args <- mapM (nextTemplate . TS.templateIdHint) tps
                let (ref, name') = case descr of
                            StructDescr l' _ _ _ -> (StructRef, C.lexemeText l')
                            UnionDescr  l' _ _ _ -> (UnionRef, C.lexemeText l')
                            EnumDescr   l' _   -> (EnumRef, C.lexemeText l')
                            IntDescr    l' _   -> (IntRef, C.lexemeText l')
                            FuncDescr   l' _ _ _ -> (FuncRef, C.lexemeText l')
                            AliasDescr  l' _ _ -> (UnresolvedRef, C.lexemeText l')
                return $ TypeRef ref (L pos ty (TS.mkId name')) args
            Nothing -> return $ TypeRef UnresolvedRef (L pos ty (TS.mkId name)) []
    Struct l@(L _ _ name) _ -> do
        ts <- State.gets tcsTypeSystem
        case lookupType name ts of
            Just descr -> do
                let tps = TypeSystem.getDescrTemplates descr
                args <- mapM (nextTemplate . TS.templateIdHint) tps
                return $ TypeRef StructRef (fmap TS.mkId l) args
            Nothing -> return $ TypeRef StructRef (fmap TS.mkId l) []
    Union l@(L _ _ name) _ -> do
        ts <- State.gets tcsTypeSystem
        case lookupType name ts of
            Just descr -> do
                let tps = TypeSystem.getDescrTemplates descr
                args <- mapM (nextTemplate . TS.templateIdHint) tps
                return $ TypeRef UnionRef (fmap TS.mkId l) args
            Nothing -> return $ TypeRef UnionRef (fmap TS.mkId l) []
    Commented _ t -> convertToTypeInfo t
    TyBitwise t -> convertToTypeInfo t
    TyForce t -> convertToTypeInfo t
    Ellipsis -> return VarArg
    _                      -> return $ BuiltinType VoidTy

replaceVoidWithTemplate :: TypeInfo 'Local -> TypeCheck (TypeInfo 'Local)
replaceVoidWithTemplate (BuiltinType VoidTy) = return $ Template (TIdAnonymous 0 Nothing) Nothing
replaceVoidWithTemplate (Const t)            = Const <$> replaceVoidWithTemplate t
replaceVoidWithTemplate (Owner t)            = Owner <$> replaceVoidWithTemplate t
replaceVoidWithTemplate (Nonnull t)          = Nonnull <$> replaceVoidWithTemplate t
replaceVoidWithTemplate (Nullable t)         = Nullable <$> replaceVoidWithTemplate t
replaceVoidWithTemplate (Qualified qs t)     = Qualified qs <$> replaceVoidWithTemplate t
replaceVoidWithTemplate (Sized t l)          = flip Sized l <$> replaceVoidWithTemplate t
replaceVoidWithTemplate (Pointer t)          = Pointer <$> replaceVoidWithTemplate t
replaceVoidWithTemplate t                    = return t


-- | Add array dimensions to a type
addArrays :: TypeInfo 'Local -> [Node (Lexeme Text)] -> TypeCheck (TypeInfo 'Local)
addArrays = foldM add
  where
    add ty (Fix (DeclSpecArray _ (Just n))) = case unFix n of
        LiteralExpr C.Int l -> return $ Array (Just ty) [IntLit (fmap TS.mkId l)]
        VarExpr l           -> return $ Array (Just ty) [NameLit (fmap TS.mkId l)]
        _ -> do
            dt <- inferExpr n
            return $ Array (Just ty) [dt]
    add ty (Fix (DeclSpecArray _ Nothing)) = return $ Array (Just ty) []
    add ty _                             = return ty


-- | Type check a statement
checkStmt :: Node (Lexeme Text) -> TypeCheck ()
checkStmt (Fix node) = atStmt (Fix node) $ do
    dtraceM $ "checkStmt: " ++ show (fmap (const ()) node)
    case node of
        CompoundStmt stmts -> mapM_ checkStmt stmts
        IfStmt cond thenB mElseB -> do
            checkExprWithExpected (BuiltinType BoolTy) cond
            checkStmt thenB
            mapM_ checkStmt mElseB
        WhileStmt cond body -> do
            checkExprWithExpected (BuiltinType BoolTy) cond
            checkStmt body
        DoWhileStmt body cond -> do
            checkStmt body
            checkExprWithExpected (BuiltinType BoolTy) cond
        ForStmt init' cond step body -> do
            checkStmt init'
            checkExprWithExpected (BuiltinType BoolTy) cond
            checkStmt step
            checkStmt body
        SwitchStmt cond cases -> do
            ct <- inferExpr cond
            rt <- resolveType ct
            if isIntOrEnum rt
                then return ()
                else reportTypeError $ SwitchConditionNotIntegral rt
            mapM_ (checkCase ct) cases
        Case _ stmt -> checkStmt stmt
        Default stmt -> checkStmt stmt
        Return mExpr -> do
            mRet <- State.gets tcsReturnType
            case (mRet, mExpr) of
                (Just ret, Just expr) -> checkExprWithExpected ret expr
                (Just (BuiltinType VoidTy), Nothing) -> return ()
                (Just ret, Nothing) -> reportTypeError $ MissingReturnValue ret
                (Nothing, _) -> return () -- Should not happen in well-formed code
        ExprStmt expr -> do
            _ <- inferExpr expr
            return ()
        VLA ty lx@(L _ _ name) expr -> do
            t <- convertToTypeInfo ty
            _ <- inferExpr expr
            State.modify $ \s -> s { tcsVars = Map.insert name (Array (Just t) [], FromDefinition name (Just lx)) (tcsVars s) }
        VarDeclStmt (Fix (VarDecl ty lx@(L _ _ name) arrs)) mInit -> do
            t <- convertToTypeInfo ty >>= flip addArrays arrs
            mapM_ (checkExprWithExpected t) mInit
            State.modify $ \s -> s { tcsVars = Map.insert name (t, FromDefinition name (Just lx)) (tcsVars s) }
        Break -> return ()
        Continue -> return ()
        Goto _ -> return ()
        Label _ stmt -> checkStmt stmt
        MacroBodyStmt body -> checkStmt body
        Group nodes -> mapM_ checkStmt nodes
        PreprocIf _ thenNodes elseNode -> do
            mapM_ checkStmt thenNodes
            checkStmt elseNode
        PreprocIfdef _ thenNodes elseNode -> do
            mapM_ checkStmt thenNodes
            checkStmt elseNode
        PreprocIfndef _ thenNodes elseNode -> do
            mapM_ checkStmt thenNodes
            checkStmt elseNode
        PreprocElse nodes -> mapM_ checkStmt nodes
        _ -> return ()


-- | Type check a function definition
checkFunctionDefn :: Node (Lexeme Text) -> TypeCheck ()
checkFunctionDefn (Fix (FunctionDefn _ (Fix (FunctionPrototype _ l@(L _ _ name) params)) body)) = withContext (InFunction name) $ do
    dtraceM $ "checkFunctionDefn: " ++ Text.unpack name
    -- Collect parameter types from this definition
    paramBindings <- mapM getParamBinding params
    let paramVars = Map.fromList [ (n, (t, FromDefinition n (Just l))) | (n, t) <- catMaybes paramBindings ]

    -- Unify with global signature from Pass 1 to connect templates
    vars <- State.gets tcsVars
    retSig <- case Map.lookup name vars of
        Just (Function ret psSig, _) -> do
            mapM_ (uncurry (\(_, tDef) tSig -> unify tSig tDef GeneralMismatch Nothing)) (zip (catMaybes paramBindings) psSig)
            return $ Just ret
        _ -> return Nothing

    -- Save current variable environment
    oldVars <- State.gets tcsVars
    oldRet <- State.gets tcsReturnType
    -- Add parameters to environment and set return type
    let funcVar = Map.singleton "__func__" (Pointer (Const (BuiltinType CharTy)), FromDefinition "__func__" (Just l))
    State.modify $ \s -> s { tcsVars = Map.union funcVar (Map.union paramVars (tcsVars s)), tcsReturnType = retSig }
    -- Check body
    checkStmt body

    -- Apply inferred bindings to the function's own signature
    -- and update the global environment
    vars' <- State.gets tcsVars
    case Map.lookup name vars' of
        Just (Function ret ps, prov) -> do
            ret' <- applyBindings ret
            ps' <- mapM applyBindings ps
            let newSig = Function ret' ps'
            dtraceM $ "Updated signature for " ++ Text.unpack name ++ ": " ++ show newSig
            -- Update oldVars with the new signature
            let oldVars' = Map.insert name (newSig, prov) oldVars
            State.modify $ \s -> s { tcsVars = oldVars', tcsReturnType = oldRet }
        _ ->
            -- Restore environment
            State.modify $ \s -> s { tcsVars = oldVars, tcsReturnType = oldRet }

    applyBindingsToTypeSystem
  where
    getParamBinding (Fix (VarDecl ty (L _ _ paramName) arrs)) = do
        t <- convertToTypeInfo ty >>= flip addArrays arrs
        return $ Just (paramName, t)
    getParamBinding (Fix (CallbackDecl (L p1 t1 ty) (L _ _ paramName))) = do
        ts <- State.gets tcsTypeSystem
        case lookupType ty ts of
            Just descr -> do
                let tps = TypeSystem.getDescrTemplates descr
                args <- mapM (nextTemplate . TS.templateIdHint) tps
                return $ Just (paramName, Pointer (TypeRef FuncRef (L p1 t1 (TS.mkId ty)) args))
            Nothing ->
                return $ Just (paramName, Pointer (TypeRef FuncRef (L p1 t1 (TS.mkId ty)) []))
    getParamBinding (Fix (NonNullParam p)) = getParamBinding p
    getParamBinding (Fix (NullableParam p)) = getParamBinding p
    getParamBinding _ = return Nothing
checkFunctionDefn _ = return ()

checkCase :: TypeInfo 'Local -> Node (Lexeme Text) -> TypeCheck ()
checkCase ct (Fix (Case label stmt)) = do
    lt <- inferExpr label
    unify ct lt GeneralMismatch (getLexeme label)
    checkStmt stmt
checkCase _ stmt = checkStmt stmt


applyBindingsToTypeSystem :: TypeCheck ()
applyBindingsToTypeSystem = do
    ts <- State.gets tcsTypeSystem
    ts' <- mapM go ts
    State.modify $ \s -> s { tcsTypeSystem = ts' }
  where
    go = \case
        StructDescr l ts mems invs -> StructDescr l ts <$> mapM (mapM (fmap TS.toGlobal . applyBindings . (TS.toLocal 0 TS.TopLevel))) mems <*> mapM (TS.mapInvariantM (fmap TS.toGlobal . applyBindings . (TS.toLocal 0 TS.TopLevel))) invs
        UnionDescr l ts mems invs -> UnionDescr l ts <$> mapM (mapM (fmap TS.toGlobal . applyBindings . (TS.toLocal 0 TS.TopLevel))) mems <*> mapM (TS.mapInvariantM (fmap TS.toGlobal . applyBindings . (TS.toLocal 0 TS.TopLevel))) invs
        FuncDescr l ts ret ps -> FuncDescr l ts <$> (TS.toGlobal <$> (applyBindings (TS.toLocal 0 TS.TopLevel ret))) <*> mapM (fmap TS.toGlobal . applyBindings . (TS.toLocal 0 TS.TopLevel)) ps
        AliasDescr l ts t -> AliasDescr l ts <$> (TS.toGlobal <$> (applyBindings (TS.toLocal 0 TS.TopLevel t)))
        t -> return t


isIntOrEnum :: TypeInfo p -> Bool
isIntOrEnum = foldFix $ \case
    BuiltinTypeF t       -> isInt t
    EnumMemF _           -> True
    TypeRefF EnumRef _ _ -> True
    QualifiedF _ t       -> t
    SizedF t _           -> t
    _                    -> False


-- | Check an expression against an expected type
checkExprWithExpected :: TypeInfo 'Local -> Node (Lexeme Text) -> TypeCheck ()
checkExprWithExpected expected expr@(Fix node) = atExpr expr $ case node of
    InitialiserList [e] -> do
        rt <- resolveType expected
        case rt of
            BuiltinType {} -> checkExprWithExpected expected e
            _              -> checkInitialiserList expected [e]
    InitialiserList exprs -> checkInitialiserList expected exprs
    _ -> do
        actual <- inferExpr expr
        unify expected actual GeneralMismatch (getLexeme expr)

checkInitialiserList :: TypeInfo 'Local -> [Node (Lexeme Text)] -> TypeCheck ()
checkInitialiserList expected exprs = do
    rt <- resolveType expected
    case rt of
        Array (Just et) _ -> mapM_ (checkExprWithExpected et) exprs
        TypeRef StructRef (L _ _ tid) args -> do
            let name = templateIdBaseName tid
            ts <- State.gets tcsTypeSystem
            case lookupType name ts of
                Just descr@(StructDescr _ _ _ _) -> do
                    let instantiated = TypeSystem.instantiateDescr 0 TS.TopLevel (Map.fromList (zip (TypeSystem.getDescrTemplates descr) args)) descr
                    case instantiated of
                        StructDescr _ _ members' _ -> do
                            let ps = map snd members'
                            let expCount = length ps
                            let actCount = length exprs
                            if actCount > expCount
                                then reportTypeError $ TooManyArgs expCount actCount
                                else mapM_ (uncurry checkExprWithExpected) (zip ps exprs)
                        _ -> error "impossible"
                _ -> reportTypeError $ UndefinedType name
        TypeRef UnionRef (L _ _ tid) args -> do
            let name = templateIdBaseName tid
            ts <- State.gets tcsTypeSystem
            case lookupType name ts of
                Just descr@(UnionDescr _ _ _ _) -> do
                    let instantiated = TypeSystem.instantiateDescr 0 TS.TopLevel (Map.fromList (zip (TypeSystem.getDescrTemplates descr) args)) descr
                    case instantiated of
                        UnionDescr _ _ members' _ -> do
                            case (members', exprs) of
                                (((_, t):_), [e]) -> checkExprWithExpected t e
                                (_, []) -> return ()
                                (_, _) -> reportError (getLexeme (Fix (InitialiserList exprs))) "union initializer must have exactly one element"
                        _ -> error "impossible"
                _ -> reportTypeError $ UndefinedType name
        _ -> do
            actual <- inferExpr (Fix (InitialiserList exprs))
            unify expected actual GeneralMismatch (getLexeme (Fix (InitialiserList exprs)))


unify :: TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> TypeCheck ()
unify expected actual reason ml = withContext (InUnification expected actual reason) $ do
    let l = ml <|> getTypeLexeme expected <|> getTypeLexeme actual
    eb1 <- resolveType =<< applyBindings expected
    ab1 <- resolveType =<< applyBindings actual
    dtraceM $ "unify: " ++ show eb1 ++ " with " ++ show ab1
    case (eb1, ab1) of
        (Template t i, a) -> bind t i a reason l
        (e, Template t i) -> bind t i e reason l
        (Nonnull (Pointer (TypeRef FuncRef name args)), Function ra pa) -> unify (Pointer (TypeRef FuncRef name args)) (Function ra pa) reason l
        (Function re pe, Nonnull (Pointer (TypeRef FuncRef name args))) -> unify (Function re pe) (Pointer (TypeRef FuncRef name args)) reason l
        (Nullable (Pointer (TypeRef FuncRef name args)), Function ra pa) -> unify (Pointer (TypeRef FuncRef name args)) (Function ra pa) reason l
        (Function re pe, Nullable (Pointer (TypeRef FuncRef name args))) -> unify (Function re pe) (Pointer (TypeRef FuncRef name args)) reason l

        (Nonnull (Pointer (TypeRef FuncRef name1 args1)), Pointer (TypeRef FuncRef name2 args2)) | name1 == name2 -> unify (Pointer (TypeRef FuncRef name1 args1)) (Pointer (TypeRef FuncRef name2 args2)) reason l
        (Nullable (Pointer (TypeRef FuncRef name1 args1)), Pointer (TypeRef FuncRef name2 args2)) | name1 == name2 -> unify (Pointer (TypeRef FuncRef name1 args1)) (Pointer (TypeRef FuncRef name2 args2)) reason l
        (Pointer (TypeRef FuncRef name1 args1), Nonnull (Pointer (TypeRef FuncRef name2 args2))) | name1 == name2 -> unify (Pointer (TypeRef FuncRef name1 args1)) (Pointer (TypeRef FuncRef name2 args2)) reason l
        (Pointer (TypeRef FuncRef name1 args1), Nullable (Pointer (TypeRef FuncRef name2 args2))) | name1 == name2 -> unify (Pointer (TypeRef FuncRef name1 args1)) (Pointer (TypeRef FuncRef name2 args2)) reason l

        (Nonnull (TypeRef FuncRef name args), Function ra pa) -> unify (TypeRef FuncRef name args) (Function ra pa) reason l
        (Function re pe, Nonnull (TypeRef FuncRef name args)) -> unify (Function re pe) (TypeRef FuncRef name args) reason l
        (Nullable (TypeRef FuncRef name args), Function ra pa) -> unify (TypeRef FuncRef name args) (Function ra pa) reason l
        (Function re pe, Nullable (TypeRef FuncRef name args)) -> unify (Function re pe) (TypeRef FuncRef name args) reason l
        (Nonnull (Pointer (Function re pe)), Pointer (TypeRef FuncRef name args)) -> unify (Function re pe) (TypeRef FuncRef name args) reason l
        (Pointer (TypeRef FuncRef name args), Nonnull (Pointer (Function ra pa))) -> unify (TypeRef FuncRef name args) (Function ra pa) reason l
        (Nullable (Pointer (Function re pe)), Pointer (TypeRef FuncRef name args)) -> unify (Function re pe) (TypeRef FuncRef name args) reason l
        (Pointer (TypeRef FuncRef name args), Nullable (Pointer (Function ra pa))) -> unify (TypeRef FuncRef name args) (Function ra pa) reason l
        (Pointer (TypeRef FuncRef name args), Pointer (Function ra pa)) -> unify (TypeRef FuncRef name args) (Function ra pa) reason l
        (Pointer (Function re pe), Pointer (TypeRef FuncRef name args)) -> unify (Function re pe) (TypeRef FuncRef name args) reason l
        (Pointer (TypeRef FuncRef tid args), Function ra pa) -> do
            let name = templateIdBaseName (C.lexemeText tid)
            ts <- State.gets tcsTypeSystem
            case lookupType name ts of
                Just descr -> do
                    let instantiated = instantiateDescr descr args
                    case instantiated of
                        FuncDescr _ _ re pe -> unify (Function re pe) (Function ra pa) reason l
                        _ -> error "impossible"
                _ -> reportTypeError $ CallingNonFunction name eb1
        (Function re pe, Pointer (TypeRef FuncRef tid args)) ->
            unify (Function re pe) (Pointer (TypeRef FuncRef tid args)) reason l
        (Pointer e', Pointer a') -> do
            if compatible eb1 ab1 || containsTemplate eb1 || containsTemplate ab1
                then unify e' a' reason l
                else reportTypeError $ TypeMismatch expected actual reason Nothing
        (Pointer e, Function ra pa) -> unify e (Function ra pa) reason l
        (Function re pe, Pointer a) -> unify (Function re pe) a reason l
        (TypeRef FuncRef tid args, Function ra pa) -> do
            let name = templateIdBaseName (C.lexemeText tid)
            ts <- State.gets tcsTypeSystem
            case lookupType name ts of
                Just descr -> do
                    let instantiated = instantiateDescr descr args
                    case instantiated of
                        FuncDescr _ _ re pe -> do
                            unify (Function re pe) (Function ra pa) reason l
                        _ -> error "impossible"
                _ -> reportTypeError $ CallingNonFunction name eb1
        (Function re pe, TypeRef FuncRef tid args) -> do
            unify (TypeRef FuncRef tid args) (Function re pe) reason l
        (TypeRef ref1 l1 args1, TypeRef ref2 l2 args2) | ref1 == ref2 && C.lexemeText l1 == C.lexemeText l2 -> do
            if not (null args1) && not (null args2) && length args1 /= length args2
                then reportError l "template argument count mismatch"
                else mapM_ (uncurry (\a1 a2 -> unify a1 a2 reason l)) (zip args1 args2)
        (Array (Just e') _, Array (Just a') _) -> do
            if compatible eb1 ab1 || containsTemplate eb1 || containsTemplate ab1
                then unify e' a' reason l
                else reportTypeError $ TypeMismatch expected actual reason Nothing
        (Array (Just e') _, Pointer a') -> do
            if compatible eb1 ab1 || containsTemplate eb1 || containsTemplate ab1
                then unify e' a' reason l
                else reportTypeError $ TypeMismatch expected actual reason Nothing
        (Pointer e', Array (Just a') _) -> do
            if compatible eb1 ab1 || containsTemplate eb1 || containsTemplate ab1
                then unify e' a' reason l
                else reportTypeError $ TypeMismatch expected actual reason Nothing
        (Function re pe, Function ra pa) -> do
            unify re ra reason l
            let expCount = length pe
            let actCount = length pa
            if actCount < expCount
                then reportTypeError $ TooFewArgs expCount actCount
                else if actCount > expCount
                    then reportTypeError $ TooManyArgs expCount actCount
                    else mapM_ (uncurry (\p1 p2 -> unify p1 p2 reason l)) (zip pe pa)

        -- Handle wrappers with recursion to allow template binding inside them
        (Qualified qs1 e, Qualified qs2 a) | qs1 == qs2 -> unify e a reason l
        (Sized e l1, Sized a l2) | l1 == l2 -> unify e a reason l

        (_, _) -> do
            if compatible eb1 ab1
                then case (eb1, ab1) of
                    (Qualified _ e, a) | isTemplate e -> unify e a reason l
                    (e, Qualified _ a) | isTemplate a -> unify e a reason l
                    (Sized e _, a) | isTemplate e     -> unify e a reason l
                    (e, Sized a _) | isTemplate a     -> unify e a reason l
                    (Qualified _ e, a)                -> unify e a reason l
                    (e, Qualified _ a)                -> unify e a reason l
                    (Sized e _, a)                    -> unify e a reason l
                    (e, Sized a _)                    -> unify e a reason l
                    _                                 -> return ()
                else reportTypeError $ TypeMismatch expected actual reason Nothing


bind :: TemplateId 'Local -> Maybe (TypeInfo 'Local) -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> TypeCheck ()
bind name index ty reason ml = do
    dtraceM $ "bind: " ++ show name ++ " to " ++ show ty
    bounds <- State.gets tcsBounds
    let k = FullTemplate name index
    case Map.lookup k bounds of
        Just (existing, _) -> do
            e' <- applyBindings existing
            t' <- applyBindings ty
            if not (compatible e' t')
                then reportTypeError $ TypeMismatch e' t' reason Nothing
                else unify e' t' reason ml
        Nothing ->
            case ty of
                Template n i | n == name && i == index -> return ()
                BuiltinType VoidTy -> return () -- Don't bind to void
                _ -> do
                    ty' <- applyBindings ty
                    ctx <- State.gets tcsContext
                    let info = ErrorInfo ml ctx (TypeMismatch (Template name index) ty' reason Nothing) []
                    State.modify $ \s -> s { tcsBounds = Map.insert k (ty', FromContext info) (tcsBounds s) }


applyBindings :: TypeInfo 'Local -> TypeCheck (TypeInfo 'Local)
applyBindings ty = applyBindingsWith Set.empty ty

applyBindingsWith :: Set (FullTemplate 'Local) -> TypeInfo 'Local -> TypeCheck (TypeInfo 'Local)
applyBindingsWith seen ty = case unFix ty of
    TemplateF (FullTemplate tid i) ->
        let k = FullTemplate tid i in
        if Set.member k seen
        then return ty
        else do
            bounds <- State.gets tcsBounds
            case Map.lookup k bounds of
                Just (target, _) -> applyBindingsWith (Set.insert k seen) target
                Nothing          -> return ty
    _ -> return ty


refreshTemplates :: TypeInfo 'Local -> TypeCheck (TypeInfo 'Local)
refreshTemplates ty = State.evalStateT (refreshTemplatesWith Set.empty ty) Map.empty

refreshTemplatesWith :: Set (FullTemplate 'Local) -> TypeInfo 'Local -> StateT (Map (FullTemplate 'Local) (TypeInfo 'Local)) TypeCheck (TypeInfo 'Local)
refreshTemplatesWith seen ty = snd (foldFix alg ty) seen
  where
    alg f = (Fix (fmap fst f), \s -> case f of
        TemplateF (FullTemplate t i) -> do
            m <- State.get
            let i_orig = fst <$> i
                k = FullTemplate t i_orig
            case Map.lookup k m of
                Just t' -> return t'
                Nothing -> do
                    i' <- if Set.member k s
                          then return Nothing
                          else maybe (return Nothing) (fmap Just . (\(_, getInner) -> getInner (Set.insert k s))) i
                    tName <- lift (nextTemplate Nothing) >>= \case
                        Template n _ -> return n
                        _ -> error "nextTemplate returned non-Template"
                    let t' = Template tName i'
                    State.modify $ Map.insert k t'
                    return t'
        _ -> Fix <$> traverse (\(_, getInner) -> getInner s) f)


-- | Check if two types are compatible (simplified)
compatible :: TypeInfo p -> TypeInfo p -> Bool
compatible t1 t2 = go Set.empty t1 t2
  where
    go seen ty1 ty2 | Set.member (ty1, ty2) seen = True
    go seen ty1 ty2 =
        let seen' = Set.insert (ty1, ty2) seen
            res = case (ty1, ty2) of
                (t1', t2') | t1' == t2' -> True
                (Template _ _, _) -> True
                (_, Template _ _) -> True
                (t1', t2') | isNetworkingStruct t1' && isNetworkingStruct t2' -> True
                (TypeRef FuncRef _ _, Function _ _) -> True
                (Function _ _, TypeRef FuncRef _ _) -> True
                (TypeRef r1 (L _ _ tid1) args1, TypeRef r2 (L _ _ tid2) args2) ->
                    r1 == r2 && tid1 == tid2 && length args1 == length args2 && all (uncurry (go seen')) (zip args1 args2)
                (ExternalType (L _ _ n1), ExternalType (L _ _ n2)) -> n1 == n2
                (Nonnull _, BuiltinType NullPtrTy) -> False
                (Pointer _, BuiltinType NullPtrTy) -> True
                (Nullable _, BuiltinType NullPtrTy) -> True
                (EnumMem _, BuiltinType t) | isInt t -> True
                (BuiltinType t, EnumMem _) | isInt t -> True
                (TypeRef EnumRef _ _, BuiltinType t) | isInt t -> True
                (BuiltinType t, TypeRef EnumRef _ _) | isInt t -> True
                (IntLit _, BuiltinType t) | isInt t -> True
                (BuiltinType t, IntLit _) | isInt t -> True
                (NameLit _, BuiltinType t) | isInt t -> True
                (BuiltinType t, NameLit _) | isInt t -> True
                (Pointer it1, Pointer it2) | isNetworkingStruct it1 && isNetworkingStruct it2 -> True
                (Pointer it1, Pointer it2) | isSockaddr it1 && isAnyStruct it2 -> True
                (Pointer it1, Pointer it2) | isAnyStruct it1 && isSockaddr it2 -> True
                (t1', t2') | isLPSTR t1' && isPointerToChar t2' -> True
                (t1', t2') | isLPSTR t2' && isPointerToChar t1' -> True
                (Pointer it1, Pointer it2) -> goPtr seen' it1 it2
                (Pointer it1, Function r ps) -> go seen' it1 (Function r ps)
                (Function r ps, Pointer it1) -> go seen' (Function r ps) it1
                (Pointer it1, Array (Just it2) _) -> goPtr seen' it1 it2
                (Array (Just it1) _, Pointer it2) -> goPtr seen' it1 it2
                (Array (Just it1) _, Array (Just it2) _) -> goPtr seen' it1 it2
                (Qualified _ it1, it2) -> go seen' it1 it2
                (it1, Qualified _ it2) -> go seen' it1 it2
                (Sized it1 _, it2) -> go seen' it1 it2
                (it1, Sized it2 _) -> go seen' it1 it2
                (Array Nothing _, Array _ _) -> True
                (Array _ _, Array Nothing _) -> True
                (TypeRef StructRef _ _, Array _ _) -> True
                (TypeRef UnionRef _ _, Array _ _) -> True
                (BuiltinType b1, BuiltinType b2)
                    | b1 == b2 -> True
                    | isInt b1 && isInt b2 -> True
                    | b1 == BoolTy && isInt b2 -> True
                    | isInt b1 && b2 == BoolTy -> True
                    | otherwise -> False
                _ -> False
        in res

    goPtr seen (Qualified qs1 it1) (Qualified qs2 it2) | qs1 == qs2 = goPtr seen it1 it2
    goPtr seen (Qualified _ it1) it2         = goPtr seen it1 it2
    goPtr seen it1 (Qualified _ it2)         = goPtr seen it1 it2
    goPtr seen (Sized it1 _) (Sized it2 _)   = goPtr seen it1 it2
    goPtr seen (Sized it1 _) it2             = goPtr seen it1 it2
    goPtr seen it1 (Sized it2 _)             = goPtr seen it1 it2
    goPtr seen it1 it2                       = go seen it1 it2

isTemplate :: TypeInfo p -> Bool
isTemplate = \case
    Template _ _ -> True
    _ -> False


-- | Collect all top-level definitions, including macros
collectDefinitions :: [Node (Lexeme Text)] -> TypeCheck ()
collectDefinitions = mapM_ collectDef
  where
    collectDef (Fix node) = case node of
        PreprocDefineMacro (L _ _ name) params body -> do
            let paramNames = mapMaybe getParamName params
            State.modify $ \s -> s { tcsMacros = Map.insert name (paramNames, body) (tcsMacros s) }
        PreprocDefineConst (L _ _ name) body -> do
            State.modify $ \s -> s { tcsMacros = Map.insert name ([], body) (tcsMacros s) }
        PreprocDefine (L _ _ _) -> return ()
        FunctionDefn _ (Fix (FunctionPrototype ty l@(L _ _ name) params)) _ -> do
            vars <- State.gets tcsVars
            if Map.member name vars && Map.member name builtinMap
                then return ()
                else do
                    retTy <- convertToTypeInfo ty
                    paramTypes <- mapM (convertToTypeInfo . getParamType) params
                    State.modify $ \s -> s { tcsVars = Map.insert name (Function retTy paramTypes, FromDefinition name (Just l)) (tcsVars s) }
        FunctionDecl _ (Fix (FunctionPrototype ty l@(L _ _ name) params)) -> do
            vars <- State.gets tcsVars
            if Map.member name vars && Map.member name builtinMap
                then return ()
                else do
                    retTy <- convertToTypeInfo ty
                    paramTypes <- mapM (convertToTypeInfo . getParamType) params
                    State.modify $ \s -> s { tcsVars = Map.insert name (Function retTy paramTypes, FromDefinition name (Just l)) (tcsVars s) }
        VarDeclStmt (Fix (VarDecl ty l@(L _ _ name) arrs)) _ -> do
            t <- convertToTypeInfo ty >>= flip addArrays arrs
            State.modify $ \s -> s { tcsVars = Map.insert name (t, FromDefinition name (Just l)) (tcsVars s) }
        ConstDecl ty l@(L _ _ name) -> do
            t <- convertToTypeInfo ty
            State.modify $ \s -> s { tcsVars = Map.insert name (t, FromDefinition name (Just l)) (tcsVars s) }
        ConstDefn _ ty l@(L _ _ name) _ -> do
            t <- convertToTypeInfo ty
            State.modify $ \s -> s { tcsVars = Map.insert name (t, FromDefinition name (Just l)) (tcsVars s) }
        AggregateDecl node' -> collectDef node'
        Typedef ty l@(L _ _ _) _ -> do
            collectDef ty
            t <- convertToTypeInfo ty
            let tg = TS.toGlobal t
            insertType l (AliasDescr l (TypeSystem.getTemplates tg) tg)
        TypedefFunction (Fix (FunctionPrototype ty (L _ _ name) params)) -> do
            retTy <- convertToTypeInfo ty
            paramTypes <- mapM (convertToTypeInfo . getParamType) params
            -- Refresh templates so that the typedef itself doesn't share global templates
            ft <- refreshTemplates (Function retTy paramTypes)
            case ft of
                Function retTy' paramTypes' -> do
                    let retTyG = TS.toGlobal retTy'
                        paramTypesG = map TS.toGlobal paramTypes'
                        templates = TypeSystem.collectTemplates (retTyG : paramTypesG)
                    dtraceM $ "TypedefFunction: " ++ Text.unpack name ++ " templates=" ++ show templates
                    State.modify $ \s -> s { tcsTypeSystem = Map.insert name (FuncDescr (L (C.AlexPn 0 0 0) C.IdVar name) templates retTyG paramTypesG) (tcsTypeSystem s) }
                _ -> error "impossible"
        Struct l@(L _ _ _) members -> do
            dtraceM $ "collectDef: Struct " ++ Text.unpack (C.lexemeText l)
            mTypes <- concat <$> mapM collectMember members
            let mTypesG = map (second TS.toGlobal) mTypes
                mTypes' = [ Var (fmap TIdName l') ty | (l', ty) <- mTypesG ]
            insertType l (StructDescr l (TypeSystem.collectTemplates mTypes') mTypesG [])
        Union l@(L _ _ _) members -> do
            mTypes <- concat <$> mapM collectMember members
            let mTypesG = map (second TS.toGlobal) mTypes
                mTypes' = [ Var (fmap TIdName l') ty | (l', ty) <- mTypesG ]
            insertType l (UnionDescr l (TypeSystem.collectTemplates mTypes') mTypesG [])
        EnumDecl l@(L _ _ _) members _ -> do
            let mNames = concatMap collectEnumNames members
            let enumTy = TypeRef EnumRef (fmap TS.mkId l) []
            forM_ mNames $ \lx@(L _ _ n) ->
                State.modify $ \s -> s { tcsVars = Map.insert n (enumTy, FromDefinition n (Just lx)) (tcsVars s) }
            insertType l (EnumDescr l (map EnumMem (map (fmap TIdName) mNames)))
        EnumConsts (Just l@(L _ _ _)) members -> do
            let mNames = concatMap collectEnumNames members
            let enumTy = TypeRef EnumRef (fmap TS.mkId l) []
            forM_ mNames $ \lx@(L _ _ n) ->
                State.modify $ \s -> s { tcsVars = Map.insert n (enumTy, FromDefinition n (Just lx)) (tcsVars s) }
            insertType l (EnumDescr l (map EnumMem (map (fmap TIdName) mNames)))
        EnumConsts Nothing members -> do
            let mNames = concatMap collectEnumNames members
            forM_ mNames $ \lx@(L _ _ n) ->
                State.modify $ \s -> s { tcsVars = Map.insert n (BuiltinType S32Ty, FromDefinition n (Just lx)) (tcsVars s) }
        Group nodes -> mapM_ collectDef nodes
        ExternC nodes -> mapM_ collectDef nodes
        PreprocIf _ thenNodes elseNode -> do
            mapM_ collectDef thenNodes
            collectDef elseNode
        PreprocIfdef _ thenNodes elseNode -> do
            mapM_ collectDef thenNodes
            collectDef elseNode
        PreprocIfndef _ thenNodes elseNode -> do
            mapM_ collectDef thenNodes
            collectDef elseNode
        PreprocElse nodes' -> mapM_ collectDef nodes'
        Commented _ node' -> collectDef node'
        CommentInfo _ -> return ()
        node' -> dtraceM $ "collectDef: skipping " ++ show (fmap (const ()) node')

    getParamName (Fix (MacroParam (L _ _ n))) = Just n
    getParamName _                            = Nothing

    collectEnumNames (Fix (Enumerator name _)) = [name]
    collectEnumNames (Fix (Commented _ node')) = collectEnumNames node'
    collectEnumNames (Fix (Group nodes'))      = concatMap collectEnumNames nodes'
    collectEnumNames _                         = []

    getParamType :: Node (Lexeme Text) -> Node (Lexeme Text)
    getParamType (Fix (VarDecl ty _ arrs)) = foldr (\_ t -> Fix (TyPointer t)) ty arrs
    getParamType (Fix (CallbackDecl (L _ _ ty) _)) = Fix (TyFunc (L (C.AlexPn 0 0 0) C.IdVar ty))
    getParamType (Fix (NonNullParam p)) = getParamType p
    getParamType (Fix (NullableParam p)) = getParamType p
    getParamType t                      = t -- Should handle more cases

    collectMember (Fix (MemberDecl (Fix (VarDecl ty (L _ _ name) arrs)) _)) = do
        t <- convertToTypeInfo ty >>= flip addArrays arrs
        dtraceM $ "collectMember: name=" ++ Text.unpack name ++ " ty=" ++ show t
        return [(L (C.AlexPn 0 0 0) C.IdVar name, t)]
    collectMember (Fix (Commented _ node')) = do
        dtraceM "collectMember: Commented"
        collectMember node'
    collectMember (Fix (Group nodes')) = do
        dtraceM "collectMember: Group"
        concat <$> mapM collectMember nodes'
    collectMember (Fix (PreprocIf _ thenNodes elseNode)) = do
        m1 <- concat <$> mapM collectMember thenNodes
        m2 <- collectMember elseNode
        return $ m1 ++ m2
    collectMember (Fix (PreprocIfdef _ thenNodes elseNode)) = do
        m1 <- concat <$> mapM collectMember thenNodes
        m2 <- collectMember elseNode
        return $ m1 ++ m2
    collectMember (Fix (PreprocIfndef _ thenNodes elseNode)) = do
        m1 <- concat <$> mapM collectMember thenNodes
        m2 <- collectMember elseNode
        return $ m1 ++ m2
    collectMember (Fix (PreprocElse nodes')) =
        concat <$> mapM collectMember nodes'
    collectMember _node'@(Fix inner) = do
        dtraceM $ "collectMember: skipping " ++ show (fmap (const ()) inner)
        return []
