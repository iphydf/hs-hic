{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module Language.Hic.TypeSystem.Core.Solver
    ( solveConstraints
    , verifyConstraints
    , applyBindings
    , collectTemplates
    , Constraint (..)
    ) where

import           Data.Fix                                   (Fix (..), foldFix,
                                                             unFix)
import           Data.Foldable                              (toList)
import           Data.List                                  (foldl', partition)
import           Data.Map.Strict                            (Map)
import qualified Data.Map.Strict                            as Map
import           Data.Maybe                                 (fromMaybe)
import           Data.Set                                   (Set)
import qualified Data.Set                                   as Set
import           Data.Text                                  (Text)
import qualified Data.Text                                  as T
import qualified Debug.Trace                                as Debug
import qualified Language.Cimple                            as C
import           Language.Hic.Core.Errors                   (Context (..),
                                                             ErrorInfo (..),
                                                             MismatchDetail (..),
                                                             MismatchReason (..),
                                                             TypeError (..))
import           Language.Hic.Core.TypeSystem               (FullTemplate,
                                                             FullTemplateF (..),
                                                             Origin (..),
                                                             Phase (..),
                                                             StdType (..),
                                                             TemplateId (..),
                                                             TypeDescr (..),
                                                             TypeInfo,
                                                             TypeInfoF (..),
                                                             TypeSystem,
                                                             collectUniqueTemplateVars,
                                                             pattern BuiltinType,
                                                             pattern FullTemplate,
                                                             pattern Qualified,
                                                             pattern Template)
import           Language.Hic.TypeSystem.Core.Base          (stripAllWrappers)
import qualified Language.Hic.TypeSystem.Core.Base          as TS
import           Language.Hic.TypeSystem.Core.Constraints
import qualified Language.Hic.TypeSystem.Core.GraphSolver   as GS
import           Language.Hic.TypeSystem.Core.Lattice
import           Language.Hic.TypeSystem.Core.Qualification (Nullability (..),
                                                             subtypeQuals)
import           Language.Hic.TypeSystem.Core.Transition    (RigidNodeF (..),
                                                             SpecialNode (..),
                                                             ValueStructure (..))
import qualified Language.Hic.TypeSystem.Core.TypeGraph     as TG

debugging :: Bool
debugging = False

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

resolveCallable :: TypeSystem -> Map (FullTemplate 'Local) (TypeInfo 'Local) -> TypeInfo 'Local -> Maybe (TypeInfo 'Local, [TypeInfo 'Local])
resolveCallable ts bindings ty =
    let rt = stripAllWrappers $ applyBindings bindings ty
    in case rt of
        TS.Function ret params -> Just (ret, params)
        TS.TypeRef TS.FuncRef (C.L _ _ tid) args ->
            let name = TS.templateIdBaseName tid
            in case TS.lookupType name ts of
                Just (TS.FuncDescr _ tps ret params) ->
                     let m = Map.fromList (zip tps args)
                         inst = TS.instantiate 0 TopLevel m
                     in Just (inst ret, map inst params)
                _ -> Nothing
        _ -> Nothing

resolveCallableG :: TypeSystem -> Map (FullTemplate 'Local) (TG.TypeGraph 'Local) -> TypeInfo 'Local -> Maybe (TG.TypeGraph 'Local, [TG.TypeGraph 'Local])
resolveCallableG ts bindings ty =
    let g = applyBindingsG bindings ty
        node = TG.getNode (TG.tgRoot g) g
    in case node of
        RFunction ret params _ _ ->
            Just (TG.TypeGraph (TG.tgNodes g) ret, map (TG.TypeGraph (TG.tgNodes g)) params)
        RValue (VPointer inner _ _) _ _ -> resolveCallableG ts bindings (TG.toTypeInfo (TG.TypeGraph (TG.tgNodes g) inner))
        RValue (VTypeRef TS.FuncRef (C.L _ _ tid) args) _ _ ->
            let name = TS.templateIdBaseName tid
            in case TS.lookupType name ts of
                Just (TS.FuncDescr _ tps ret params) ->
                     let argTys = map (TG.toTypeInfo . TG.TypeGraph (TG.tgNodes g)) args
                         m = Map.fromList (zip tps argTys)
                         inst = TS.instantiate 0 TopLevel m
                     in Just (TG.fromTypeInfo (inst ret), map (TG.fromTypeInfo . inst) params)
                _ -> Nothing
        _ -> Nothing

-- | Solves a list of constraints for a given set of templates.
-- Uses SCC-based graph reduction to find the least specific
-- types that satisfy all constraints.
solveConstraints :: TypeSystem -> Set Integer -> Map (FullTemplate 'Local) (TypeInfo 'Local) -> [Constraint 'Local] -> Map (FullTemplate 'Local) (TypeInfo 'Local)
solveConstraints ts activePhases initialBindingsMap constraints =
    let initialBindingsG = Map.map TG.fromTypeInfo initialBindingsMap
        -- Pass 1: Structural constraints
        g1 = buildConstraintGraph constraints
        s1 = GS.solveAll g1 (Map.keys g1)
        b1 = Map.union s1 initialBindingsG

        -- Pass 2: Activate HasMember/Callable using Pass 1 results
        g2 = foldl' (activateConstraints b1) g1 constraints
        s2 = GS.solveAll g2 (Map.keys g2)
        b2 = Map.union s2 initialBindingsG

        -- Pass 3: One more activation for dependencies between HasMember and Callable
        g3 = foldl' (activateConstraints b2) g2 constraints
        s3 = GS.solveAll g3 (Map.keys g3)
        finalBindings = Map.union s3 initialBindingsG
    in Map.mapWithKey (\ft tyG -> let ty = TG.toTypeInfo tyG in if isUnconstrained ty then Fix (TemplateF ft) else ty) finalBindings
  where
    isUnconstrained TS.Unconstrained = True
    isUnconstrained _                = False

    activateConstraints bindings graph = \case
        HasMember base field memberTy _ _ _ ->
            let gBase = applyBindingsG bindings base
                go g = let node = TG.getNode (TG.tgRoot g) g in case node of
                    RValue (VPointer inner _ _) _ _ -> go (TG.TypeGraph (TG.tgNodes g) inner)
                    RValue (VTypeRef _ (C.L _ _ tid) args) _ _ ->
                        let name = TS.templateIdBaseName tid
                        in case TS.lookupType name ts of
                            Just descr ->
                                let argTys = map (TG.toTypeInfo . TG.TypeGraph (TG.tgNodes g)) args
                                    descr' = TS.instantiateDescr 0 TopLevel (Map.fromList (zip (TS.getDescrTemplates descr) argTys)) descr
                                in case TS.lookupMemberType field descr' of
                                    Just t -> decomposeEqualityG (addEdgeG graph memberTy (TG.fromTypeInfo t)) (TG.fromTypeInfo memberTy) (TG.fromTypeInfo t)
                                    Nothing -> graph
                            Nothing -> graph
                    _ -> graph
            in go gBase

        Callable funcType argTypes returnType _ _ mCsId shouldRefresh ->
            let refreshedFunc = if shouldRefresh then refreshTemplates activePhases mCsId funcType (Map.map TG.toTypeInfo bindings) else funcType
                vFunc = applyBindingsG bindings refreshedFunc
                node = TG.getNode (TG.tgRoot vFunc) vFunc
            in case resolveCallableG ts bindings refreshedFunc of
                Just (retG, paramsG) ->
                    let g0 = decomposeEqualityG graph (TG.fromTypeInfo returnType) retG
                    in foldl' (\g (pG, a) -> decomposeSubtypeG g (TG.fromTypeInfo a) pG) g0 (zip paramsG argTypes)
                Nothing ->
                    case node of
                        RValue (VTemplate ft _ _) _ _ ->
                            let tid = TS.ftId ft
                                baseIdx = case tid of
                                    TIdSolver idx _    -> idx * 100
                                    TIdPoly ph idx _ _ -> fromIntegral ph * 1000 + idx * 100
                                    TIdInst idx _      -> fromIntegral idx * 100
                                    _                  -> 0
                                mkT j h = Fix (TemplateF (FullTemplate (TIdSolver (baseIdx + j) (Just h)) Nothing))
                                retT = mkT 99 "ret"
                                argTs = [ mkT j "arg" | j <- [0..length argTypes - 1] ]
                                funcVal = TS.Function retT argTs
                            in let g0 = decomposeEqualityG graph vFunc (TG.fromTypeInfo funcVal)
                                   g1 = decomposeEqualityG g0 (TG.fromTypeInfo returnType) (TG.fromTypeInfo retT)
                               in foldl' (\g (p, a) -> decomposeSubtypeG g (TG.fromTypeInfo a) (TG.fromTypeInfo p)) g1 (zip argTs argTypes)
                        _ -> graph
        CoordinatedPair trigger actual expected _ _ _ ->
            let gTrigger = applyBindingsG bindings trigger
                node = TG.getNode (TG.tgRoot gTrigger) gTrigger
                isNonnull = case node of
                    RValue (VPointer _ n _) _ _         -> n /= QNullable'
                    RValue (VTemplate _ n _) _ _        -> n /= QNullable'
                    RFunction {}                        -> True
                    RValue (VBuiltin NullPtrTy) _ _     -> False
                    RValue (VSingleton NullPtrTy _) _ _ -> False
                    _                                   -> False
            in if isNonnull
               then decomposeSubtypeG graph (TG.fromTypeInfo actual) (TG.fromTypeInfo expected)
               else graph
        _ -> graph

    buildConstraintGraph cs =
        let initial = Map.fromList [ (t, Set.empty) | t <- concatMap collectTemplates cs ]
            -- Structural decomposition: if T = S1 and T = S2, then S1 = S2.
            -- This pushes constraints down into nested templates.
            expanded = structuralDecomposition initial cs
            graphWithTys = foldl' addConstraint initial expanded
        in Map.map (Set.map TG.fromTypeInfo) graphWithTys

    structuralDecomposition initial cs =
        let g = foldl' addConstraint initial cs
            implied = concatMap (extractImplied g) (Map.keys g)
            newImplied = filter (`notElem` cs) implied
        in if null newImplied then cs else structuralDecomposition initial (cs ++ newImplied)

    extractImplied graph ft =
        let values = Set.toList $ Map.findWithDefault Set.empty ft graph
            (templates, structs) = partition isTemplate values
        in case structs of
            (s:ss) -> [Equality s s' Nothing [] GeneralMismatch | s' <- ss] ++
                      [Equality s t Nothing [] GeneralMismatch | t <- templates]
            [] -> case templates of
                (t:ts_) -> [Equality t t' Nothing [] GeneralMismatch | t' <- ts_]
                [] -> []

    addConstraint graph = \case
        Equality t1 t2 _ _ _ -> decomposeEquality graph t1 t2
        Subtype actual expected _ _ _ -> decomposeSubtype graph actual expected
        Lub t t_list _ _ _ ->
            foldl' (\acc t_in -> decomposeLub acc t t_in) graph t_list
        _ -> graph

    decomposeEquality graph t1 t2 =
        case (unFix t1, unFix t2) of
            (TemplateF _, TemplateF _) ->
                addEdge (addEdge graph t1 t2) t2 t1
            (TemplateF _, _) -> addEdge graph t1 t2
            (_, TemplateF _) -> addEdge graph t2 t1
            (PointerF a, PointerF b) -> decomposeEquality graph a b
            (ArrayF (Just a) _, ArrayF (Just b) _) -> decomposeEquality graph a b
            (FunctionF r1 p1, FunctionF r2 p2) | length p1 == length p2 ->
                let gRet = decomposeEquality graph r1 r2
                in foldl' (\g (pp1, pp2) -> decomposeEquality g pp1 pp2) gRet (zip p1 p2)
            (QualifiedF qs1 a, QualifiedF qs2 b) | qs1 == qs2 -> decomposeEquality graph a b
            (VarF _ a, VarF _ b) -> decomposeEquality graph a b
            -- Structural mismatch: no assignment can make these equal.
            _ -> markConflict graph [t1, t2]

    decomposeSubtype graph actual expected =
        case (unFix actual, unFix expected) of
            (TemplateF _, TemplateF _) ->
                addEdge (addEdge graph actual expected) expected actual
            (TemplateF _, _) -> addEdge graph actual expected
            (_, TemplateF _) -> addEdge graph expected actual
            (PointerF a, PointerF b) -> decomposeSubtype graph a b
            (ArrayF (Just a) _, ArrayF (Just b) _) -> decomposeSubtype graph a b
            (FunctionF r1 p1, FunctionF r2 p2) | length p1 == length p2 ->
                let gRet = decomposeSubtype graph r1 r2
                -- Contravariant parameters: expected <: actual for parameters
                in foldl' (\g (pActual, pExpected) -> decomposeSubtype g pExpected pActual) gRet (zip p1 p2)
            (QualifiedF qs1 a, QualifiedF qs2 b) ->
                if subtypeQuals qs1 qs2 then decomposeSubtype graph a b else markConflict graph [actual, expected]
            (VarF _ a, VarF _ b) -> decomposeSubtype graph a b
            -- Peeling wrappers
            (QualifiedF qs a, b) ->
                if subtypeQuals qs Set.empty then decomposeSubtype graph a (Fix b) else markConflict graph [actual, expected]
            (a, QualifiedF es b) ->
                if subtypeQuals Set.empty es then decomposeSubtype graph (Fix a) b else markConflict graph [actual, expected]
            -- Structural mismatch: no assignment can satisfy this subtype relationship.
            _ -> markConflict graph [actual, expected]

    -- | Decompose a Lub constraint: t_in <: t (each list element is a lower bound for the target).
    -- When the target contains templates wrapped in structure, we push requirements
    -- into nested templates.  On structural mismatch, any templates in the target
    -- are marked Conflict because no assignment can satisfy the constraint.
    decomposeLub graph t t_in =
        case (unFix t, unFix t_in) of
            -- Target is a bare template: add t_in as a lower bound.
            (TemplateF _, _) -> addEdge graph t t_in
            -- Element is a bare template: add t as its lower bound (t_in <: t).
            (_, TemplateF _) -> addEdge graph t_in t
            -- Bottom is <: anything; skip.
            (_, ConflictF) -> graph
            -- Top is always a valid upper bound; skip.
            (_, UnconstrainedF) -> graph
            -- Matching structure: decompose into children.
            (PointerF a, PointerF b) -> decomposeLub graph a b
            (ArrayF (Just a) _, ArrayF (Just b) _) -> decomposeLub graph a b
            (FunctionF r1 p1, FunctionF r2 p2) | length p1 == length p2 ->
                -- Covariant return: r_in <: r  (accumulate lower bounds for r's templates)
                let gRet = decomposeLub graph r1 r2
                -- Contravariant params: p <: p_in  (use subtype decomposition)
                in foldl' (\g (pTarget, pIn) -> decomposeSubtype g pTarget pIn) gRet (zip p1 p2)
            (QualifiedF qs1 a, QualifiedF qs2 b) | subtypeQuals qs2 qs1 -> decomposeLub graph a b
            (VarF _ a, VarF _ b) -> decomposeLub graph a b
            -- Structural mismatch: mark all templates in both sides as Conflict.
            _ -> markConflict graph [t, t_in]

    decomposeEqualityG graph g1 g2 =
        let t1 = TG.toTypeInfo g1
            t2 = TG.toTypeInfo g2
        in case (unFix t1, unFix t2) of
            (TemplateF _, TemplateF _) ->
                addEdgeG (addEdgeG graph t1 g2) t2 g1
            (TemplateF _, _) -> addEdgeG graph t1 g2
            (_, TemplateF _) -> addEdgeG graph t2 g1
            (PointerF a, PointerF b) -> decomposeEqualityG graph (TG.fromTypeInfo a) (TG.fromTypeInfo b)
            (ArrayF (Just a) _, ArrayF (Just b) _) -> decomposeEqualityG graph (TG.fromTypeInfo a) (TG.fromTypeInfo b)
            (FunctionF r1 p1, FunctionF r2 p2) | length p1 == length p2 ->
                let gRet = decomposeEqualityG graph (TG.fromTypeInfo r1) (TG.fromTypeInfo r2)
                in foldl' (\g (pp1, pp2) -> decomposeEqualityG g (TG.fromTypeInfo pp1) (TG.fromTypeInfo pp2)) gRet (zip p1 p2)
            (QualifiedF qs1 a, QualifiedF qs2 b) | qs1 == qs2 -> decomposeEqualityG graph (TG.fromTypeInfo a) (TG.fromTypeInfo b)
            (VarF _ a, VarF _ b) -> decomposeEqualityG graph (TG.fromTypeInfo a) (TG.fromTypeInfo b)
            _ -> graph

    decomposeSubtypeG graph g1 g2 =
        let t1 = TG.toTypeInfo g1
            t2 = TG.toTypeInfo g2
        in case (unFix t1, unFix t2) of
            (TemplateF _, TemplateF _) ->
                addEdgeG (addEdgeG graph t1 g2) t2 g1
            (TemplateF _, _) -> addEdgeG graph t1 g2
            (_, TemplateF _) -> addEdgeG graph t2 g1
            (PointerF a, PointerF b) -> decomposeSubtypeG graph (TG.fromTypeInfo a) (TG.fromTypeInfo b)
            (ArrayF (Just a) _, ArrayF (Just b) _) -> decomposeSubtypeG graph (TG.fromTypeInfo a) (TG.fromTypeInfo b)
            (FunctionF r1 p1, FunctionF r2 p2) | length p1 == length p2 ->
                let gRet = decomposeSubtypeG graph (TG.fromTypeInfo r1) (TG.fromTypeInfo r2)
                -- Contravariant parameters: expected <: actual for parameters
                in foldl' (\g (pActual, pExpected) -> decomposeSubtypeG g (TG.fromTypeInfo pExpected) (TG.fromTypeInfo pActual)) gRet (zip p1 p2)
            (QualifiedF qs1 a, QualifiedF qs2 b) ->
                if subtypeQuals qs1 qs2 then decomposeSubtypeG graph (TG.fromTypeInfo a) (TG.fromTypeInfo b) else graph
            (VarF _ a, VarF _ b) -> decomposeSubtypeG graph (TG.fromTypeInfo a) (TG.fromTypeInfo b)
            -- Peeling wrappers
            (QualifiedF qs a, _) ->
                if subtypeQuals qs Set.empty then decomposeSubtypeG graph (TG.fromTypeInfo a) g2 else graph
            (_, QualifiedF es b) ->
                if subtypeQuals Set.empty es then decomposeSubtypeG graph g1 (TG.fromTypeInfo b) else graph
            _ -> graph

    -- | Mark all templates in the given types as Conflict (unsatisfiable constraint).
    markConflict graph tys =
        let templates = collectUniqueTemplateVars tys
        in foldl' (\g ft -> Map.insertWith Set.union ft (Set.singleton TS.Conflict) g) graph templates

    addEdge graph (Fix (TemplateF ft)) val =
        let res = if ft `elem` TS.collectUniqueTemplateVars [val]
                  then Map.insertWith Set.union ft (Set.singleton (TS.Unsupported "recursive type")) graph
                  else Map.insertWith Set.union ft (Set.singleton val) graph
        in dtrace ("addEdge " ++ show ft ++ " -> " ++ show val) res
    addEdge graph _ _ = graph

    addEdgeG graph (Fix (TemplateF ft)) valG =
        let res = if ft `elem` TS.collectUniqueTemplateVars [TG.toTypeInfo valG]
                  then Map.insertWith Set.union ft (Set.singleton (TG.fromTypeInfo (TS.Unsupported "recursive type"))) graph
                  else Map.insertWith Set.union ft (Set.singleton valG) graph
        in dtrace ("addEdgeG " ++ show ft ++ " -> " ++ show (TG.toTypeInfo valG)) res
    addEdgeG graph _ _ = graph

applyBindingsG :: Map (FullTemplate 'Local) (TG.TypeGraph 'Local) -> TypeInfo 'Local -> TG.TypeGraph 'Local
applyBindingsG bindings ty =
    let g = TG.fromTypeInfo ty
        vars = TS.collectUniqueTemplateVars [ty]
    in foldl (\acc v -> case Map.lookup v bindings of
                            Just vG | not (isUnconstrainedG vG) -> TG.minimizeGraph $ TG.substitute v vG acc
                            _ -> acc) g vars
  where
    isUnconstrainedG gRes = case TG.getNode (TG.tgRoot gRes) gRes of
        RSpecial SUnconstrained -> True
        _                       -> False

isTemplate :: TypeInfo p -> Bool
isTemplate (Fix (TemplateF _)) = True
isTemplate _                   = False

refreshTemplates :: Set Integer -> Maybe Integer -> TypeInfo 'Local -> Map (FullTemplate 'Local) (TypeInfo 'Local) -> TypeInfo 'Local
refreshTemplates activePhases mCsId ty bindings =
    case mCsId of
        Just csId -> foldFix (alg csId) ty
        Nothing   -> ty
  where
    alg :: Integer -> TypeInfoF (TemplateId 'Local) (TypeInfo 'Local) -> TypeInfo 'Local
    alg csId f = case f of
        TemplateF (FullTemplate tid mIdx) ->
            case tid of
                TIdPoly ph idx h _ | not (Set.member ph activePhases) ->
                    -- Use current binding for the template if it exists
                    let current = applyBindings bindings (Fix f)
                    in if not (isTemplate current || current == TS.Unconstrained)
                       then current
                       else Template (TIdInst csId (TS.TIdParam idx h TopLevel)) mIdx
                _ -> Fix f
        _ -> Fix f

applyBindings :: Map (FullTemplate 'Local) (TypeInfo 'Local) -> TypeInfo 'Local -> TypeInfo 'Local
applyBindings bindings ty = go Set.empty ty
  where
    go seen t = case unFix t of
        TemplateF ft ->
            if Set.member ft seen
            then t
            else case Map.lookup ft bindings of
                Just TS.Unconstrained -> t
                Just ty'              -> go (Set.insert ft seen) ty'
                Nothing               -> t
        f -> Fix $ fmap (go seen) f

-- | Verifies that all constraints are satisfied by the given bindings.
-- Returns a list of errors for unsatisfied constraints.
verifyConstraints :: TypeSystem -> Set Integer -> Map (FullTemplate 'Local) (TypeInfo 'Local) -> [Constraint 'Local] -> [ErrorInfo 'Local]
verifyConstraints ts activePhases bindings constraints =
    concatMap verify constraints
  where
    verify = \case
        Equality t1 t2 ml ctx r ->
            let v1 = applyBindings bindings t1
                v2 = applyBindings bindings t2
            in if v1 == v2
               then []
               else [ErrorInfo ml (InUnification v1 v2 r : ctx) (TypeMismatch v1 v2 r (Just (BaseMismatch v1 v2))) []]

        Subtype actual expected ml ctx r ->
            let vActual = applyBindings bindings actual
                vExpected = applyBindings bindings expected
            in if subtypeOf vActual vExpected
               then []
               else [ErrorInfo ml (InUnification vExpected vActual r : ctx) (TypeMismatch vExpected vActual r (Just (BaseMismatch vExpected vActual))) []]

        HasMember base field memberTy ml ctx r ->
            let vBase = stripAllWrappers $ applyBindings bindings base
                vMemberTy = applyBindings bindings memberTy
            in case vBase of
                TS.TypeRef _ (C.L _ _ tid) args ->
                    let name = TS.templateIdBaseName tid
                    in case TS.lookupType name ts of
                        Just descr ->
                            let descr' = TS.instantiateDescr 0 TopLevel (Map.fromList (zip (TS.getDescrTemplates descr) args)) descr
                            in case TS.lookupMemberType field descr' of
                                Just t ->
                                    if subtypeOf t vMemberTy
                                    then []
                                    else [ErrorInfo ml ctx (TypeMismatch vMemberTy t r (Just (BaseMismatch vMemberTy t))) []]
                                Nothing -> [ErrorInfo ml ctx (CustomError $ "member " <> field <> " not found in struct " <> name) []]
                        Nothing -> [ErrorInfo ml ctx (CustomError $ "struct " <> name <> " not found") []]
                _ -> [ErrorInfo ml ctx (TypeMismatch (BuiltinType TS.VoidTy) vBase r (Just (BaseMismatch (BuiltinType TS.VoidTy) vBase))) []]

        Callable funcType argTypes returnType ml ctx mCsId shouldRefresh ->
            let vFuncOrig = applyBindings bindings funcType
                vFunc = if shouldRefresh
                        then refreshTemplates activePhases mCsId vFuncOrig bindings
                        else vFuncOrig
            in dtrace ("verify Callable: vFunc=" ++ show vFunc) $ case resolveCallable ts bindings vFunc of
                Just (ret, params) ->
                    let vRet = applyBindings bindings ret
                        vReturnType = applyBindings bindings returnType
                        errRet = if subtypeOf vRet vReturnType
                                 then []
                                 else dtrace ("  Return mismatch: ret=" ++ show vRet ++ " returnType=" ++ show vReturnType) [ErrorInfo ml ctx (TypeMismatch vReturnType vRet GeneralMismatch (Just (BaseMismatch vReturnType vRet))) []]
                        errArity =
                            let isVariadic = any TS.isVarArg params
                                fixedParams = filter (not . TS.isVarArg) params
                                nFixed = length fixedParams
                                nActual = length argTypes
                            in if nActual < nFixed
                               then [ErrorInfo ml ctx (TooFewArgs nFixed nActual) []]
                               else if nActual > nFixed && not isVariadic
                               then [ErrorInfo ml ctx (TooManyArgs nFixed nActual) []]
                               else []
                        errArgs = concat [ let vA = applyBindings bindings a
                                               vP = applyBindings bindings p
                                           in dtrace ("  Arg check: vA=" ++ show vA ++ " vP=" ++ show vP) $ if TS.isVarArg vP || subtypeOf vA vP
                                              then []
                                              else dtrace "    Mismatch!" [ErrorInfo ml ctx (TypeMismatch vP vA GeneralMismatch (Just (BaseMismatch vP vA))) []]
                                         | (p, a) <- zip params argTypes ]
                    in errRet ++ errArity ++ errArgs
                Nothing -> [ErrorInfo ml ctx (CallingNonFunction "expression" vFunc) []]

        CoordinatedPair trigger actual expected ml ctx _mCsId ->
            let vTrigger = applyBindings bindings trigger
                isNonnull = \case
                    TS.Nonnull _ -> True
                    TS.Pointer _ -> True
                    _ -> False
            in if isNonnull vTrigger
               then let vActual = applyBindings bindings actual
                        vExpected = applyBindings bindings expected
                    in if subtypeOf vActual vExpected
                       then []
                       else [ErrorInfo ml ctx (TypeMismatch vExpected vActual GeneralMismatch (Just (BaseMismatch vExpected vActual))) []]
               else []

        Lub t t_list ml ctx r ->
            let vT = applyBindings bindings t
                vTs = map (applyBindings bindings) t_list
            in concat [ if subtypeOf vTi vT
                        then []
                        else [ErrorInfo ml (InUnification vT vTi r : ctx) (TypeMismatch vT vTi r (Just (BaseMismatch vT vTi))) []]
                      | vTi <- vTs ]
