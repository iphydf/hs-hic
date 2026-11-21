{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TupleSections       #-}
module Language.Hic.Refined.Inference.Translator
    ( translateRegistry
    , translateDescr
    , translateMember
    , translateType
    , translateType'
    , translateReturnType
    , translateTemplateIdGlobal
    , nodeToTypeInfo
    , translateStdType
    , translateTypePhysical
    ) where

import           Control.Monad.State.Strict                  (State, get, gets,
                                                              modify)
import           Data.Fix                                    (Fix (..), foldFix)
import qualified Data.Map.Strict                             as Map
import           Data.Maybe                                  (fromMaybe)
import qualified Data.Set                                    as Set
import           Data.Text                                   (Text)
import qualified Data.Text                                   as T
import qualified Data.Text.Read                              as TR
import           Data.Word                                   (Word32)

import           Language.Cimple                             (Lexeme (..))
import qualified Language.Cimple                             as C
import           Language.Hic.Refined.Inference.Substitution
import           Language.Hic.Refined.Inference.Types
import           Language.Hic.Refined.Inference.Utils
import           Language.Hic.Refined.LatticeOp
import           Language.Hic.Refined.Registry
import           Language.Hic.Refined.Types
import qualified Language.Hic.TypeSystem.Core.Base           as TS

translateRegistry :: TS.TypeSystem -> State TranslatorState (Registry Word32)
translateRegistry ts = do
    modify $ \s -> s { tsOwnParams = ownParams ts }
    -- Functions get their types from their prototypes; their descriptions in
    -- the type system carry every template parameter of their arguments, and
    -- aren't types anything is declared with.
    defs <- Map.traverseWithKey (\_ d -> translateDescr d) (Map.filter (not . isFunction) ts)
    return $ Registry defs
  where
    isFunction = \case
        TS.FuncDescr{} -> True
        _              -> False

-- | Which of each struct's, union's and function typedef's parameters in the
-- type system are its own: those of its storage. The type system's list also
-- has the parameters of every struct it points to, which aren't this one's, as
-- each object pointed to has its own (read through the pointer as skolems of
-- that object).
ownParams :: TS.TypeSystem -> Map.Map Text [Bool]
ownParams ts = Map.mapMaybe (fmap (mask Set.empty) . storage) ts
  where
    storage = \case
        TS.FuncDescr _ ps ret args -> Just (ps, ret : args)
        descr                      -> fmap (fmap (map snd)) (members descr)

    members = \case
        TS.StructDescr _ ps ms _ -> Just (ps, ms)
        TS.UnionDescr _ ps ms _  -> Just (ps, ms)
        _                        -> Nothing

    mask visited (ps, tys) = map (`Set.member` foldMap (storageVars visited) tys) ps

    -- The visited set stops at a struct already being looked at, which only
    -- a pointer back to it can reach.
    storageVars visited (Fix ty) = case ty of
        TS.PointerF target | isStruct ts (unqualified target) -> Set.empty
        TS.TemplateF (TS.FT tid _) -> Set.singleton tid
        TS.TypeRefF _ (L _ _ tid) args
            | name <- TS.templateIdBaseName tid
            , Just (ps, ms) <- members =<< TS.lookupType name ts ->
                if name `Set.member` visited then Set.empty else
                foldMap (storageVars visited) (knownArgs (mask (Set.insert name visited) (ps, map snd ms)) args)
        _ -> foldMap (storageVars visited) ty

    unqualified = \case
        Fix (TS.QualifiedF _ t) -> unqualified t
        Fix (TS.SizedF t _)     -> unqualified t
        t                       -> t

-- | Whether a type is a reference to a struct or union.
isStruct :: TS.TypeSystem -> TS.TypeInfo 'TS.Global -> Bool
isStruct ts = \case
    Fix (TS.TypeRefF _ (L _ _ tid) _) -> case TS.lookupType (TS.templateIdBaseName tid) ts of
        Just TS.StructDescr{} -> True
        Just TS.UnionDescr{}  -> True
        _                     -> False
    _ -> False

-- | The arguments of a reference at the parameters marked own. In a group of
-- types that refer to each other, the type system gives a reference the
-- parameters its target had when the reference was resolved, which can be
-- fewer than it ends up with: those arguments match no parameters, and the
-- reference is to some instance.
knownArgs :: [Bool] -> [a] -> [a]
knownArgs own args
    | length own == length args = [ arg | (True, arg) <- zip own args ]
    | otherwise                 = []

-- | What a pointer points to. A struct behind a pointer is another object,
-- with its own parameters: field access through the pointer reads them as
-- skolems of that object ('memberOf'), so the struct has no arguments, and is
-- any instance.
translatePointee :: TS.TypeInfo 'TS.Global -> State TranslatorState Word32
translatePointee inner = do
    ts <- gets tsTypeSystem
    let resolved = TS.resolveRef ts inner
        TS.FlatType {..} = TS.toFlat resolved
    case ftStructure of
        TS.TypeRefF _ name _ | isStruct ts (Fix ftStructure) ->
            register $ AnyRigidNodeF (RObject (VNominal (fmap translateTemplateIdGlobal name) []) (Quals (TS.QConst `Set.member` ftQuals) False))
        _ -> translateType inner

-- | The type system's arguments of a struct, at its own parameters ('ownParams').
ownArgs :: Text -> [a] -> State TranslatorState [a]
ownArgs name args = do
    masks <- gets tsOwnParams
    return $ maybe args (`knownArgs` args) (Map.lookup name masks)

translateDescr :: TS.TypeDescr 'TS.Global -> State TranslatorState (TypeDefinition Word32)
translateDescr = \case
    TS.StructDescr name params members _ -> do
        memberDefs <- mapM translateMember members
        ps <- ownArgs (C.lexemeText name) params
        return $ StructDef name (map ((, Invariant) . translateTemplateIdGlobal) ps) memberDefs
    TS.UnionDescr name params members _ -> do
        memberDefs <- mapM translateMember members
        ps <- ownArgs (C.lexemeText name) params
        return $ UnionDef name (map ((, Invariant) . translateTemplateIdGlobal) ps) memberDefs
    TS.EnumDescr name _ ->
        return $ EnumDef name []
    TS.IntDescr name _ ->
        return $ EnumDef name []
    TS.FuncDescr name params _ _ ->
        return $ StructDef name (map ((, Invariant) . translateTemplateIdGlobal) params) []
    TS.AliasDescr name params _ ->
        return $ StructDef name (map ((, Invariant) . translateTemplateIdGlobal) params) []


nodeToTypeInfo :: TS.TypeSystem -> C.Node (Lexeme Text) -> TS.TypeInfo 'TS.Global
nodeToTypeInfo ts (Fix node) = case node of
    C.TyStd l -> TS.builtin l
    C.TyPointer t -> TS.Pointer (nodeToTypeInfo ts t)
    C.FunctionPrototype ret _ params ->
        TS.Function (nodeToTypeInfo ts ret) (map (nodeToTypeInfo ts) params)
    C.VarDecl ty _ dims ->
        let baseTy = nodeToTypeInfo ts ty
            -- An array without a size (x[]) has no dimension.
            sizes = [ nodeToTypeInfo ts size | Fix (C.DeclSpecArray _ (Just size)) <- dims ]
            -- The first brackets say whether it's nullable (x[_Nullable N]).
            nullability = case dims of
                Fix (C.DeclSpecArray n _) : _ -> TS.arrayNullability n
                _                             -> id
        in if null dims then baseTy else nullability (TS.Array (Just baseTy) sizes)
    C.DeclSpecArray _ mSize -> maybe TS.Unconstrained (nodeToTypeInfo ts) mSize
    C.TyConst t -> TS.Const (nodeToTypeInfo ts t)
    C.TyNonnull t -> TS.Nonnull (nodeToTypeInfo ts t)
    C.TyNullable t -> TS.Nullable (nodeToTypeInfo ts t)
    C.TyOwner t -> TS.Owner (nodeToTypeInfo ts t)
    C.TyUserDefined (L _ _ t) -> case TS.lookupType t ts of
        Just (TS.AliasDescr _ _ target) -> target
        _ -> TS.TypeRef TS.UnresolvedRef (L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName t)) []
    C.TyStruct l -> TS.TypeRef TS.StructRef (fmap TS.TIdName l) []
    C.TyUnion l -> TS.TypeRef TS.UnionRef (fmap TS.TIdName l) []
    C.TyFunc l -> TS.TypeRef TS.FuncRef (fmap TS.TIdName l) []
    C.VarExpr l -> TS.TypeRef TS.UnresolvedRef (fmap TS.TIdName l) []
    C.LiteralExpr C.Int l -> TS.IntLit (fmap TS.TIdName l)
    f -> TS.Unsupported (T.pack (show (Fix f)))

translateMember :: (Lexeme Text, TS.TypeInfo 'TS.Global) -> State TranslatorState (Member Word32)
translateMember (name, ty) = do
    tyId <- translateType ty
    return $ Member name tyId

-- | Translates a standard Cimple type to a Refined RigidNode,
-- favoring the existential form if it exists.
translateTypePack :: TS.TypeInfo 'TS.Global -> State TranslatorState Word32
translateTypePack ty = do
    st <- get
    let ty' = TS.resolveRef (tsTypeSystem st) ty
    let TS.FlatType {..} = TS.toFlat ty'
    case ftStructure of
        TS.TypeRefF _ name _ -> do
            let baseName = TS.templateIdBaseName (C.lexemeText name)
            case Map.lookup baseName (tsExistentials st) of
                Just existId -> return existId
                Nothing      -> translateType ty
        _ -> translateType ty

-- | Translates a standard Cimple type to a Refined RigidNode.
translateType :: TS.TypeInfo 'TS.Global -> State TranslatorState Word32
translateType = translateType'' False

-- | Translates a standard Cimple type to a Refined RigidNode,
-- marking the top-level structure as physically immutable.
translateTypePhysical :: TS.TypeInfo 'TS.Global -> State TranslatorState Word32
translateTypePhysical = translateType'' True

translateType'' :: Bool -> TS.TypeInfo 'TS.Global -> State TranslatorState Word32
translateType'' physical ty = do
    st <- get
    let ty' = TS.resolveRef (tsTypeSystem st) ty

    let fresh = isFreshCandidate ty'
    -- Only cache types without void or anonymous templates: each void* is
    -- its own template. A struct's parameters belong to its definition, so
    -- types using them are shared.
    -- Also don't cache if we are forcing physical constancy, as it might
    -- conflict with a non-physical cache entry.
    mId <- if fresh || physical then return Nothing else gets (Map.lookup ty' . tsCache)
    case mId of
        Just nid -> return nid
        Nothing -> do
            nid <- gets tsNextId
            modify $ \s -> s { tsNextId = nid + 1 }
            if not fresh && not physical then
                modify $ \s -> s { tsCache = Map.insert ty' nid (tsCache s) }
            else return ()
            node <- translateType' ty'
            let node' = if physical then setPhysical node else node
            dtraceM ("Registering ID " ++ show nid ++ ": " ++ show node')
            modify (addNode nid node')
            return nid
  where
    isFreshCandidate = foldFix (\case
        TS.BuiltinTypeF TS.VoidTy -> True
        TS.TemplateF (TS.FT tid _) -> case tid of
            TS.TIdAnonymous {} -> True
            _                  -> False
        f -> any id f)

    setPhysical (AnyRigidNodeF (RObject s q)) = AnyRigidNodeF (RObject s (q { qPhysical = True }))
    setPhysical (AnyRigidNodeF (RReference s n o q)) = AnyRigidNodeF (RReference s n o (q { qPhysical = True }))
    setPhysical n = n

translateType' :: TS.TypeInfo 'TS.Global -> State TranslatorState (AnyRigidNodeF TemplateId Word32)
translateType' ty = do
    let TS.FlatType {..} = TS.toFlat ty
    dtraceM ("translateType': ftStructure=" ++ show (fmap (const ()) ftStructure))
    let isConst = TS.QConst `Set.member` ftQuals
        -- Physical constancy is currently only inferred for literals and forced top-level decls.
        quals = Quals isConst False
        nullability = if TS.QNonnull `Set.member` ftQuals then QNonnull'
                      else if TS.QNullable `Set.member` ftQuals then QNullable'
                      else QUnspecified
        ownership = if TS.QOwner `Set.member` ftQuals then QOwned' else QNonOwned'
    case ftStructure of
        TS.BuiltinTypeF TS.VoidTy -> do
            nid <- gets tsNextId
            let tid = TIdParam PLocal nid (Just "T")
            modify $ \s -> s { tsNextId = nid + 1 }
            modify (addNode nid (AnyRigidNodeF (RObject (VVar tid Nothing) quals)))
            return $ AnyRigidNodeF (RObject (VVar tid Nothing) quals)

        TS.BuiltinTypeF bt -> case translateStdType bt of
            Just sbt -> return $ AnyRigidNodeF (RObject (VBuiltin sbt) quals)
            Nothing  -> dtrace ("Translator SConflict at BuiltinTypeF: " ++ show bt) $ return $ AnyRigidNodeF (RTerminal SConflict)

        TS.PointerF inner -> do
            let (Fix innerF) = inner
            case innerF of
                TS.FunctionF ret args -> do
                    retId <- translateReturnType ret
                    argIds <- mapM translateType args
                    return $ AnyRigidNodeF (RReference (Ptr (TargetFunction argIds retId)) nullability ownership quals)
                TS.TypeRefF TS.FuncRef name refArgs -> do
                    st <- get
                    let typedef = TS.templateIdBaseName (C.lexemeText name)
                    case TS.lookupType typedef (tsTypeSystem st) of
                        Just (TS.FuncDescr _ params ret args) -> do
                            -- The signature's parameters are the reference's
                            -- arguments, not the typedef's variables. A
                            -- reference has arguments for all of them, or for
                            -- its own ('knownArgs').
                            let own = maybe params (\m -> [ p | (True, p) <- zip m params ]) (Map.lookup typedef (tsOwnParams st))
                                bound | length params == length refArgs = zip params refArgs
                                      | length own == length refArgs    = zip own refArgs
                                      | otherwise                       = []
                                instantiate = TS.instantiateGlobal (Map.fromList bound)
                            retId <- translateReturnType (instantiate ret)
                            argIds <- mapM (translateType . instantiate) args
                            return $ AnyRigidNodeF (RReference (Ptr (TargetFunction argIds retId)) nullability ownership quals)
                        _ -> do
                            innerId <- translateType inner
                            return $ AnyRigidNodeF (RReference (Ptr (TargetObject innerId)) nullability ownership quals)
                TS.BuiltinTypeF TS.VoidTy -> do
                    varNid <- gets tsNextId
                    let tid = TIdParam PLocal varNid (Just "T")
                    modify $ \s -> s { tsNextId = varNid + 1 }
                    modify (addNode varNid (AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))))
                    return $ AnyRigidNodeF (RReference (Ptr (TargetOpaque tid)) nullability ownership quals)
                _ -> do
                    innerId <- translatePointee inner
                    return $ AnyRigidNodeF (RReference (Ptr (TargetObject innerId)) nullability ownership quals)

        TS.FunctionF ret args -> do
            retId <- translateReturnType ret
            argIds <- mapM translateType args
            return $ AnyRigidNodeF (RFunction argIds retId)

        TS.ArrayF (Just inner) dims -> do
            innerId <- translateTypePack inner
            dimIds <- mapM translateType dims
            return $ AnyRigidNodeF (RReference (Arr innerId dimIds) nullability ownership quals)

        TS.TypeRefF _ name params -> do
            paramIds <- mapM translateType =<< ownArgs (TS.templateIdBaseName (C.lexemeText name)) params
            return $ AnyRigidNodeF (RObject (VNominal (fmap translateTemplateIdGlobal name) paramIds) quals)

        TS.TemplateF (TS.FT tid _) -> do
            return $ AnyRigidNodeF (RObject (VVar (translateTemplateIdGlobal tid) Nothing) quals)

        TS.SingletonF st val -> case translateStdType st of
            Just sbt -> return $ AnyRigidNodeF (RObject (VSingleton sbt val) (Quals True True))
            Nothing  -> dtrace ("Translator SConflict at SingletonF: " ++ show st) $ return $ AnyRigidNodeF (RTerminal SConflict)

        TS.IntLitF l -> do
            let t = TS.templateIdToText (C.lexemeText l)
            case TR.decimal t of
                Right (i, _) -> return $ AnyRigidNodeF (RObject (VSingleton S32Ty i) (Quals True True))
                Left _       -> dtrace ("Translator SAny at IntLitF (invalid decimal): " ++ show t) $ return $ AnyRigidNodeF (RTerminal SAny)

        TS.NameLitF l ->
            return $ AnyRigidNodeF (RObject (VEnum (fmap translateTemplateIdGlobal l)) quals)

        TS.EnumMemF l ->
            return $ AnyRigidNodeF (RObject (VEnum (fmap translateTemplateIdGlobal l)) quals)

        TS.ExternalTypeF l ->
            return $ AnyRigidNodeF (RObject (VNominal (fmap translateTemplateIdGlobal l) []) quals)

        TS.UnconstrainedF ->
            return $ AnyRigidNodeF (RTerminal SAny)

        TS.ConflictF ->
            return $ AnyRigidNodeF (RTerminal SConflict)

        TS.ProxyF inner ->
            translateType' inner

        ft -> dtrace ("Translator SAny at catch-all: " ++ show ft) $ return $ AnyRigidNodeF (RTerminal SAny)

translateReturnType :: TS.TypeInfo 'TS.Global -> State TranslatorState (ReturnType Word32)
translateReturnType (Fix (TS.BuiltinTypeF TS.VoidTy)) = return RetVoid
translateReturnType ty = RetVal <$> translateType ty

translateTemplateIdGlobal :: TS.TemplateId 'TS.Global -> TemplateId
translateTemplateIdGlobal = \case
    TS.TIdName n        -> TIdName n
    TS.TIdParam i h _   -> TIdParam PGlobal (fromIntegral i) h
    TS.TIdAnonymous _ h -> TIdName (fromMaybe "ANON" h)
    TS.TIdRec i         -> TIdName ("REC" <> T.pack (show i))

translateStdType :: TS.StdType -> Maybe StdType
translateStdType = \case
    TS.BoolTy    -> Just BoolTy
    TS.CharTy    -> Just CharTy
    TS.U08Ty     -> Just U08Ty
    TS.S08Ty     -> Just S08Ty
    TS.U16Ty     -> Just U16Ty
    TS.S16Ty     -> Just S16Ty
    TS.U32Ty     -> Just U32Ty
    TS.S32Ty     -> Just S32Ty
    TS.U64Ty     -> Just U64Ty
    TS.S64Ty     -> Just S64Ty
    TS.SizeTy    -> Just SizeTy
    TS.F32Ty     -> Just F32Ty
    TS.F64Ty     -> Just F64Ty
    TS.NullPtrTy -> Just NullPtrTy
    TS.VoidTy    -> Nothing
