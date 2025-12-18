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
    defs <- Map.traverseWithKey (\_ d -> translateDescr d) ts
    return $ Registry defs

translateDescr :: TS.TypeDescr 'TS.Global -> State TranslatorState (TypeDefinition Word32)
translateDescr = \case
    TS.StructDescr name params members _ -> do
        memberDefs <- mapM translateMember members
        return $ StructDef name (map ((, Invariant) . translateTemplateIdGlobal) params) memberDefs
    TS.UnionDescr name params members _ -> do
        memberDefs <- mapM translateMember members
        return $ UnionDef name (map ((, Invariant) . translateTemplateIdGlobal) params) memberDefs
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
        in if null dims then baseTy else TS.Array (Just baseTy) (map (nodeToTypeInfo ts) dims)
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
    -- Only cache non-void types to ensure freshness for void*
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
            TS.TIdParam {}     -> True
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
                TS.TypeRefF TS.FuncRef name _ -> do
                    st <- get
                    case TS.lookupType (TS.templateIdBaseName (C.lexemeText name)) (tsTypeSystem st) of
                        Just (TS.FuncDescr _ _ ret args) -> do
                            retId <- translateReturnType ret
                            argIds <- mapM translateType args
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
                    innerId <- translateType inner
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
            paramIds <- mapM translateType params
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
