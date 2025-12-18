{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData          #-}
{-# LANGUAGE TupleSections       #-}
module Language.Hic.TypeSystem.Core.Base
    ( module Language.Hic.Core.TypeSystem
    , getTypeRefName
    , lookupType
    , insert
    , foldArray
    , vars
    , builtin
    , getTemplates
    , collectTemplates
    , collectTemplateVars
    , collectTypes
    , collect
    , normalizeDescr
    , resolve
    , deVoidify
    , toLocal
    , toGlobal
    , toGlobalId
    , getBaseOrigin
    , getOriginLineage
    , typeDescrToType
    , setOrigin
    , instantiateInvariant
    , renameStateful
    , renameTemplates
    , instantiateDescr
    , instantiate
    , PhaseOps (..)
    , getTypeParams
    , getDescrTemplates
    , getDescrLexeme
    , mkId
    , resolveRef
    , resolveRefLocal
    , indexTemplates
    , mapTemplates
    , isInt
    , unwrap
    , stripAllWrappers
    , isPointerLike
    , getInnerType
    , promoteNonnull
    , lookupMemberType
    , descrToTypeInfo
    , isVarArg
    , isSpecial
    , promote
    , containsTemplate
    , isGeneric
    , isSockaddr
    , isSockaddrIn
    , isSockaddrIn6
    , isSockaddrStorage
    , isNetworkingStruct
    , isAnyStruct
    , getTypeLexeme
    , resolveType'
    , isLPSTR
    , isPointerToChar
    , instantiateGlobal
    ) where

import           Control.Applicative                   ((<|>))

import           Control.Arrow                         (second)
import           Data.Bifunctor                        (bimap, first)

import           Control.Monad                         (forM_)
import           Control.Monad.State.Strict            (State)
import qualified Control.Monad.State.Strict            as State
import           Data.Fix                              (Fix (..), foldFix,
                                                        foldFixM)
import           Data.Foldable                         (fold, toList)
import           Data.List                             (foldl')
import           Data.Map.Strict                       (Map)

import qualified Data.Graph                            as Graph
import qualified Data.Map.Strict                       as Map
import           Data.Maybe                            (fromMaybe)
import           Data.Set                              (Set)
import qualified Data.Set                              as Set
import           Data.Text                             (Text)
import qualified Data.Text                             as Text
import qualified Debug.Trace                           as Debug
import           Language.Cimple                       (Lexeme (..),
                                                        LiteralType (..), Node,
                                                        NodeF (..), lexemeText)
import qualified Language.Cimple                       as C
import           Language.Hic.Core.TypeSystem          (ArbitraryTemplateId (..),
                                                        FlatType (..),
                                                        FullTemplate,
                                                        FullTemplateF (..),
                                                        Invariant (..),
                                                        Origin (..), Phase (..),
                                                        Qualifier (..),
                                                        StdType (..),
                                                        TemplateId (..),
                                                        TypeDescr (..),
                                                        TypeInfo,
                                                        TypeInfoF (..),
                                                        TypeRef (..),
                                                        TypeSystem,
                                                        collectUniqueTemplateVars,
                                                        fromFlat,
                                                        getTemplateVars,
                                                        isConflict,
                                                        isUnconstrained, isVoid,
                                                        mapInvariant,
                                                        mapInvariantM,
                                                        normalizeQuals,
                                                        normalizeType,
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
                                                        pattern Unsupported,
                                                        pattern Var,
                                                        pattern VarArg,
                                                        stripLexemes,
                                                        templateIdBaseName,
                                                        templateIdHint,
                                                        templateIdOrigin,
                                                        templateIdToText,
                                                        toFlat,
                                                        voidFullTemplate,
                                                        zipWithF)
import           Language.Hic.TypeSystem.Core.Builtins (builtins)


debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg = if debugging then Debug.trace msg else id


getTypeRefName :: TypeInfo p -> Maybe (TemplateId p)
getTypeRefName = foldFix $ \case
    TypeRefF _ (L _ _ tid) _ -> Just tid
    PointerF tid                -> tid
    QualifiedF _ tid            -> tid
    _                         -> Nothing


lookupType :: Text -> TypeSystem -> Maybe (TypeDescr 'Global)
lookupType name ts =
    let res = go Set.empty name
    in dtrace ("lookupType " ++ Text.unpack name ++ " -> " ++ show (fmap getDescrLexeme res)) res
  where
    p = C.AlexPn 0 0 0
    go visited n
        | Set.member n visited = Nothing
        | otherwise =
            case Map.lookup n ts <|> Map.lookup n builtins of
                Just (AliasDescr _ _ target) ->
                    case getTypeRefName target of
                        Just tid -> go (Set.insert n visited) (templateIdBaseName tid)
                        Nothing   -> case target of
                            TypeRef StructRef (L _ _ (TIdName "")) _ -> Map.lookup "" ts
                            TypeRef UnionRef  (L _ _ (TIdName "")) _ -> Map.lookup "" ts
                            _ -> Just (AliasDescr (L p C.IdVar n) [] target)
                Nothing -> Nothing
                res -> res

insert :: Lexeme Text -> TypeDescr 'Global -> State CollectState [TypeInfo 'Global]
insert name ty = do
    let nameText = lexemeText name
    existing <- State.gets (Map.lookup nameText . fst)
    case (ty, existing) of
        -- If we have a typedef that points to a struct/union/enum of the same name,
        -- and we already have the definition, ignore the typedef.
        (AliasDescr _ _ (TypeRef _ (L _ _ tid) _), Just StructDescr{}) | templateIdBaseName tid == nameText ->
            return [TypeRef UnresolvedRef (fmap TIdName name) []]
        (AliasDescr _ _ (TypeRef _ (L _ _ tid) _), Just UnionDescr{})  | templateIdBaseName tid == nameText ->
            return [TypeRef UnresolvedRef (fmap TIdName name) []]
        (AliasDescr _ _ (TypeRef _ (L _ _ tid) _), Just EnumDescr{})   | templateIdBaseName tid == nameText ->
            return [TypeRef UnresolvedRef (fmap TIdName name) []]

        -- If we are adding a definition and we have a typedef of the same name
        -- that points to this name, overwrite it.
        (StructDescr{}, Just (AliasDescr _ _ (TypeRef _ (L _ _ tid) _))) | templateIdBaseName tid == nameText -> do
            State.modify . first $ Map.insert nameText ty
            return [TypeRef UnresolvedRef (fmap TIdName name) []]
        (UnionDescr{}, Just (AliasDescr _ _ (TypeRef _ (L _ _ tid) _)))  | templateIdBaseName tid == nameText -> do
            State.modify . first $ Map.insert nameText ty
            return [TypeRef UnresolvedRef (fmap TIdName name) []]

        -- Merge struct/union definitions, keeping the one with members.
        (StructDescr _ _ mems _, Just (StructDescr _ _ existingMems _)) -> do
            if null existingMems && not (null mems)
                then State.modify . first $ Map.insert nameText ty
                else return ()
            return [TypeRef UnresolvedRef (fmap TIdName name) []]
        (UnionDescr _ _ mems _, Just (UnionDescr _ _ existingMems _)) -> do
            if null existingMems && not (null mems)
                then State.modify . first $ Map.insert nameText ty
                else return ()
            return [TypeRef UnresolvedRef (fmap TIdName name) []]

        _ -> do
            State.modify . first $ Map.insert nameText ty
            return [TypeRef UnresolvedRef (fmap TIdName name) []]

foldArray :: Lexeme Text -> [[TypeInfo 'Global]] -> TypeInfo 'Global -> TypeInfo 'Global
foldArray name arrs baseTy = Var (fmap TIdName name) (merge baseTy (concat arrs))
  where
    merge ty (Array Nothing dims:xs) = merge (Array (Just ty) dims) xs
    merge ty []                      = ty
    merge ty xs                      = error (show (ty, xs))


vars :: [[TypeInfo 'Global]] -> [(Lexeme Text, TypeInfo 'Global)]
vars = map (\(ln, ty) -> (fmap templateIdBaseName ln, ty)) . joinSizer . map go . concat
  where
    go (Var name ty) = (name, ty)
    go x             = error $ show x

    joinSizer (d@(dn@(L _ _ dnameTid), dty@Array{}):s@(sn@(L _ _ snameTid), BuiltinType U32Ty):xs)
        | let dname = templateIdBaseName dnameTid
        , let sname = templateIdBaseName snameTid
        , sname `elem` [dname <> "_length", dname <> "_size"] =
            (dn, Sized dty sn) : joinSizer xs
        | otherwise = d : joinSizer (s:xs)
    joinSizer (d@(dn@(L _ _ dnameTid), dty@Pointer{}):s@(sn@(L _ _ snameTid), BuiltinType U32Ty):xs)
        | let dname = templateIdBaseName dnameTid
        , let sname = templateIdBaseName snameTid
        , sname `elem` [dname <> "_length", dname <> "_size"] =
            (dn, Sized dty sn) : joinSizer xs
        | otherwise = d : joinSizer (s:xs)
    joinSizer (d@(dn@(L _ _ dnameTid), dty@(Owner Pointer{})):s@(sn@(L _ _ snameTid), BuiltinType U32Ty):xs)
        | let dname = templateIdBaseName dnameTid
        , let sname = templateIdBaseName snameTid
        , sname `elem` [dname <> "_length", dname <> "_size"] =
            (dn, Sized dty sn) : joinSizer xs
        | otherwise = d : joinSizer (s:xs)
    joinSizer (d@(dn@(L _ _ dnameTid), dty@(Nonnull Pointer{})):s@(sn@(L _ _ snameTid), BuiltinType U32Ty):xs)
        | let dname = templateIdBaseName dnameTid
        , let sname = templateIdBaseName snameTid
        , sname `elem` [dname <> "_length", dname <> "_size"] =
            (dn, Sized dty sn) : joinSizer xs
        | otherwise = d : joinSizer (s:xs)
    joinSizer (d@(dn@(L _ _ dnameTid), dty@(Nullable Pointer{})):s@(sn@(L _ _ snameTid), BuiltinType U32Ty):xs)
        | let dname = templateIdBaseName dnameTid
        , let sname = templateIdBaseName snameTid
        , sname `elem` [dname <> "_length", dname <> "_size"] =
            (dn, Sized dty sn) : joinSizer xs
        | otherwise = d : joinSizer (s:xs)
    joinSizer (x:xs) = x:joinSizer xs
    joinSizer []     = []


builtin :: Lexeme Text -> TypeInfo 'Global
builtin (L _ _              "char")  = BuiltinType CharTy
builtin (L _ _           "uint8_t")  = BuiltinType U08Ty
builtin (L _ _            "int8_t")  = BuiltinType S08Ty
builtin (L _ _          "uint16_t")  = BuiltinType U16Ty
builtin (L _ _           "int16_t")  = BuiltinType S16Ty
builtin (L _ _          "uint32_t")  = BuiltinType U32Ty
builtin (L _ _           "int32_t")  = BuiltinType S32Ty
builtin (L _ _          "uint64_t")  = BuiltinType U64Ty
builtin (L _ _           "int64_t")  = BuiltinType S64Ty
builtin (L _ _            "size_t")  = BuiltinType SizeTy
builtin (L _ _         "ssize_t")    = BuiltinType S64Ty
builtin (L _ _         "socklen_t")  = BuiltinType U32Ty
builtin (L _ _         "in_addr_t")  = BuiltinType U32Ty
builtin (L _ _         "in_port_t")  = BuiltinType U16Ty
builtin (L _ _       "sa_family_t")  = BuiltinType U16Ty
builtin (L _ _             "DWORD")  = BuiltinType U32Ty
builtin (L _ _            "LPDWORD") = Pointer (BuiltinType U32Ty)
builtin (L _ _              "WORD")  = BuiltinType U16Ty
builtin (L _ _              "BYTE")  = BuiltinType U08Ty
builtin (L _ _               "INT")  = BuiltinType S32Ty
builtin (L _ _             "LPINT")  = Pointer (BuiltinType S32Ty)
builtin (L _ _            "u_long")  = BuiltinType U32Ty
builtin (L _ _            "LPCSTR")  = Pointer (Const (BuiltinType CharTy))
builtin (L p t          "LPSTR")   = TypeRef UnresolvedRef (L p t (TIdName "LPSTR")) []
builtin (L p t          "LPSOCKADDR") = Pointer (TypeRef StructRef (L p t (TIdName "sockaddr")) [])
builtin (L _ _              "void")  = BuiltinType VoidTy
builtin (L _ _              "bool")  = BuiltinType BoolTy
builtin (L _ _             "float")  = BuiltinType F32Ty
builtin (L _ _            "double")  = BuiltinType F64Ty

builtin (L _ _               "int")  = BuiltinType S32Ty
builtin (L _ _              "long")  = BuiltinType S64Ty
builtin (L _ _     "unsigned long")  = BuiltinType U64Ty
builtin (L _ _      "unsigned int")  = BuiltinType U32Ty
builtin (L _ _          "unsigned")  = BuiltinType U32Ty
builtin (L _ _   "long signed int")  = BuiltinType S64Ty
builtin (L _ _ "long unsigned int")  = BuiltinType U64Ty

builtin (L p t "OpusEncoder")      = ExternalType (L p t (TIdName "OpusEncoder"))
builtin (L p t "OpusDecoder")      = ExternalType (L p t (TIdName "OpusDecoder"))
builtin (L p t "cmp_ctx_t")        = ExternalType (L p t (TIdName "cmp_ctx_t"))
builtin (L p t "pthread_mutex_t")     = ExternalType (L p t (TIdName "pthread_mutex_t"))
builtin (L p t "pthread_mutexattr_t") = ExternalType (L p t (TIdName "pthread_mutexattr_t"))
builtin (L p t "pthread_rwlock_t")    = ExternalType (L p t (TIdName "pthread_rwlock_t"))
builtin (L p t "pthread_rwlockattr_t") = ExternalType (L p t (TIdName "pthread_rwlockattr_t"))
builtin (L p t "vpx_codec_ctx_t")     = ExternalType (L p t (TIdName "vpx_codec_ctx_t"))
builtin (L p t "va_list")          = ExternalType (L p t (TIdName "va_list"))

builtin (L p t name)               = TypeRef UnresolvedRef (L p t (TIdName name)) []


collectTemplateVars :: [TypeInfo 'Global] -> [FullTemplate 'Global]
collectTemplateVars tys =
    let uniqueRaw = collectUniqueTemplateVars tys
        mkTid i t = TIdParam i (templateIdHint $ ftId t) TopLevel
    in [ FullTemplate (mkTid i t) Nothing | (i, t) <- zip [(0::Int)..] uniqueRaw ]

normalizeDescr :: [TypeInfo 'Global] -> ([TypeInfo 'Global], [TemplateId 'Global])
normalizeDescr tys =
    let vt = collectTemplateVars tys
        ts = map ftId vt
        tys' = State.evalState (mapM renameStateful tys) (Map.empty, vt)
    in (tys', ts)

normalizeMems :: [(Lexeme Text, TypeInfo 'Global)] -> ([(Lexeme Text, TypeInfo 'Global)], [TemplateId 'Global])
normalizeMems mems =
    let (tys', ts) = normalizeDescr [ Var (fmap TIdName l) ty | (l, ty) <- mems ]
        unVar (Var _ t) = t
        unVar t         = t
        mems' = zip (map fst mems) (map unVar tys')
    in (mems', ts)

getTemplates :: TypeInfo p -> [TemplateId p]
getTemplates ty = map ftId $ getTemplateVars ty

collectTemplates :: [TypeInfo p] -> [TemplateId p]
collectTemplates tys = map ftId $ collectTemplateVars' tys
  where
    collectTemplateVars' :: [TypeInfo p] -> [FullTemplate p]
    collectTemplateVars' ts =
        let uniqueRaw = collectUniqueTemplateVars ts
        in [ FullTemplate (ftId t) Nothing | t <- uniqueRaw ]

collectTypes :: NodeF (Lexeme Text) [TypeInfo 'Global] -> State CollectState [TypeInfo 'Global]
collectTypes node = case node of
    LiteralExpr ConstId name     -> return [NameLit (fmap TIdName name)]
    LiteralExpr Int lit          -> return [IntLit (fmap TIdName lit)]

    DeclSpecArray _ Nothing        -> return []
    DeclSpecArray _ (Just arr)     -> return [Array Nothing arr]
    CallbackDecl ty name         -> return [Var (fmap TIdName name) (TypeRef FuncRef (fmap TIdName ty) [])]
    VarDecl ty name []           -> return $ map (Var (fmap TIdName name)) ty
    VarDecl ty name arrs         -> return $ map (foldArray name arrs) ty
    MemberDecl l _               -> return l
    Struct dcl mems              -> aggregate (\l m -> let (m', ts) = normalizeMems m in dtrace ("TypeSystem Struct: " ++ Text.unpack (lexemeText dcl) ++ " templates=" ++ show ts) $ StructDescr l ts m' []) dcl mems
    Union  dcl mems              -> aggregate (\l m -> let (m', ts) = normalizeMems m in dtrace ("TypeSystem Union: " ++ Text.unpack (lexemeText dcl) ++ " templates=" ++ show ts) $ UnionDescr  l ts m' []) dcl mems

    Enumerator name _            -> return [EnumMem (fmap TIdName name)]
    EnumConsts (Just dcl) mems   -> enum dcl mems
    EnumDecl dcl mems _          -> enum dcl mems
    Typedef [BuiltinType ty] dcl _ -> insert dcl (AliasDescr dcl [] (BuiltinType ty))
    Typedef [ty] dcl _             -> case normalizeDescr [ty] of
                                      ([ty'], ts) -> insert dcl (AliasDescr dcl ts ty')
                                      _ -> error "normalizeDescr returned empty list"

    FunctionPrototype ty name params -> return [Var (fmap TIdName name) (Function t (concat params)) | t <- ty]
    TypedefFunction a -> do
        forM_ a $ \case
            Var name (Function ret params) -> do
                let nameTid = lexemeText name
                let nameText = case nameTid of TIdName n -> n; _ -> ""
                case normalizeDescr (ret:params) of
                    (ret':params', templates) -> do
                        dtrace ("TypeSystem TypedefFunction: " ++ Text.unpack nameText ++ " templates=" ++ show templates) $
                          State.modify . first $ Map.insert nameText (FuncDescr (fmap (const nameText) name) templates ret' params')
                    _ -> error "normalizeDescr returned empty list"
            _ -> return ()
        return a

    TyUserDefined name           -> return [TypeRef UnresolvedRef (fmap TIdName name) []]
    TyStruct name                -> return [TypeRef StructRef (fmap TIdName name) []]
    TyUnion name                 -> return [TypeRef UnionRef (fmap TIdName name) []]
    TyFunc name                  -> return [TypeRef FuncRef (fmap TIdName name) []]
    TyPointer ns                 -> return $ map (Pointer . deVoidify) ns
    TyConst ns                   -> return $ map Const ns
    TyOwner ns                   -> return $ map Owner ns
    TyNonnull ns                 -> return $ map Nonnull ns
    TyNullable ns                -> return $ map Nullable ns

    TyStd name                   -> return [builtin name]

    Ellipsis                     -> return [VarArg]

    FunctionDecl _ vars' -> do
        dtrace ("TypeSystem FunctionDecl: " ++ show vars') $ case vars' of
            [Var name (Function ret params)] -> do
                let nameText = case lexemeText name of TIdName n -> n; _ -> ""
                case normalizeDescr (ret:params) of
                    (ret':params', templates) ->
                        State.modify . first $ Map.insert nameText (FuncDescr (fmap (const nameText) name) templates ret' params')
                    _ -> error "normalizeDescr returned empty list"
            _ -> return ()
        return []
    FunctionDefn _ vars' _ -> do
        dtrace ("TypeSystem FunctionDefn: " ++ show vars') $ case vars' of
            [Var name (Function ret params)] -> do
                let nameText = case lexemeText name of TIdName n -> n; _ -> ""
                case normalizeDescr (ret:params) of
                    (ret':params', templates) ->
                        State.modify . first $ Map.insert nameText (FuncDescr (fmap (const nameText) name) templates ret' params')
                    _ -> error "normalizeDescr returned empty list"
            _ -> return ()
        return []

    PreprocDefineConst name _ -> do
        State.modify . first $ Map.insert (lexemeText name) (AliasDescr (fmap (const $ lexemeText name) name) [] (BuiltinType S32Ty))
        return []

    PreprocDefine name -> do
        State.modify . first $ Map.insert (lexemeText name) (AliasDescr (fmap (const $ lexemeText name) name) [] (BuiltinType S32Ty))
        return []

    ConstDefn _ [ty] name _ -> return [Var (fmap TIdName name) ty]

    -- The rest just collects all the types it sees.
    n                            -> return $ concat n

  where
    aggregate cons dcl mems = insert dcl (cons dcl (vars mems))
    enum dcl mems = insert dcl (EnumDescr dcl (concat mems))


type CollectState = (TypeSystem, Int)

collect :: [(FilePath, [Node (Lexeme Text)])] -> TypeSystem
collect programList =
    resolve . fst . flip State.execState (Map.empty, 0) . mapM_ (mapM_ (foldFixM collectTypes) . snd) $ programList

getDeps :: TypeDescr 'Global -> [Text]
getDeps = \case
    StructDescr _ _ mems invs -> concatMap (getFreeRefs . snd) mems ++ concatMap getInvDeps invs
    UnionDescr _ _ mems invs  -> concatMap (getFreeRefs . snd) mems ++ concatMap getInvDeps invs
    EnumDescr _ mems -> concatMap getFreeRefs mems
    FuncDescr _ _ ret ps -> getFreeRefs ret ++ concatMap getFreeRefs ps
    AliasDescr _ _ ty -> getFreeRefs ty
    _ -> []
  where
    getFreeRefs = foldFix $ \case
        TypeRefF _ (L _ _ tid) args -> templateIdBaseName tid : concat args
        f -> fold f
    getInvDeps = \case
        InvCallable f as r -> getFreeRefs f ++ concatMap getFreeRefs as ++ getFreeRefs r
        InvEquality t1 t2  -> getFreeRefs t1 ++ getFreeRefs t2
        InvSubtype t1 t2   -> getFreeRefs t1 ++ getFreeRefs t2
        InvCoordinatedPair t1 t2 t3 -> getFreeRefs t1 ++ getFreeRefs t2 ++ getFreeRefs t3

resolve :: TypeSystem -> TypeSystem
resolve tys =
    let -- Step 1: Build dependency graph
        edges = [ (name, name, getDeps descr) | (name, descr) <- Map.toList tys ]
        sccs = Graph.stronglyConnComp edges

        -- Step 2: Process SCCs in topological order (Graph.stronglyConnComp returns them leaves-first)
        finalTys = foldl' resolveScc tys sccs
    in finalTys
  where
    resolveScc acc (Graph.AcyclicSCC name) =
        case Map.lookup name acc of
            Just descr ->
                let seen = Set.singleton name
                    descr' = resolveRefs seen acc descr
                    descr'' = reCollect' seen acc descr'
                in Map.insert name descr'' acc
            Nothing -> acc
    resolveScc acc (Graph.CyclicSCC names) =
        -- For cyclic SCCs, we need at most two passes to stabilize signatures,
        -- but since C doesn't allow recursive aliases, it's usually stable in one.
        -- We run it twice to be absolutely sure of normalization stability.
        let seen = Set.fromList names
            acc' = foldl' (resolveInMap (resolveRefs seen)) acc names
            acc'' = foldl' (resolveInMap (reCollect' seen)) acc' names
        in acc''

    resolveInMap f m name =
        case Map.lookup name m of
            Just descr -> Map.insert name (f m descr) m
            Nothing    -> m

    resolveRefs seen currentTys = \case
        StructDescr dcl ts mems invs -> StructDescr dcl ts (map (second (resolveRefWith seen currentTys)) mems) invs
        UnionDescr dcl ts mems invs -> UnionDescr dcl ts (map (second (resolveRefWith seen currentTys)) mems) invs
        FuncDescr dcl ts ret params -> FuncDescr dcl ts (resolveRefWith seen currentTys ret) (map (resolveRefWith seen currentTys) params)
        AliasDescr dcl ts ty' -> AliasDescr dcl ts (resolveRefWith seen currentTys ty')
        ty -> ty

    reCollect' seen currentTys = \case
        StructDescr dcl _ mems invs ->
            let mems' = map (second (resolveRefWith seen currentTys)) mems
                (mems'', ts) = normalizeMems mems'
                res = StructDescr dcl ts mems'' invs
            in dtrace ("reCollect Struct: " ++ Text.unpack (lexemeText dcl) ++ " templates=" ++ show ts) res
        UnionDescr dcl _ mems invs ->
            let mems' = map (second (resolveRefWith seen currentTys)) mems
                (mems'', ts) = normalizeMems mems'
                res = UnionDescr dcl ts mems'' invs
            in dtrace ("reCollect Union: " ++ Text.unpack (lexemeText dcl) ++ " templates=" ++ show ts) res
        FuncDescr dcl _ ret params ->
            let ret' = resolveRefWith seen currentTys ret
                params' = map (resolveRefWith seen currentTys) params
            in case normalizeDescr (ret':params') of
                (ret'':params'', ts) ->
                    FuncDescr dcl ts ret'' params''
                _ -> error "normalizeDescr returned empty list"
        AliasDescr dcl _ ty' ->
            let ty'' = resolveRefWith seen currentTys ty'
            in case normalizeDescr [ty''] of
                ([ty'''], ts) ->
                    AliasDescr dcl ts ty'''
                _ -> error "normalizeDescr returned empty list"
        ty -> ty

deVoidify :: TypeInfo p -> TypeInfo p
deVoidify = id

renameStateful :: TypeInfo p -> State (Map (FullTemplate p) (TypeInfo p), [FullTemplate p]) (TypeInfo p)
renameStateful = foldFix alg
  where
    alg :: TypeInfoF (TemplateId p) (State (Map (FullTemplate p) (TypeInfo p), [FullTemplate p]) (TypeInfo p)) -> State (Map (FullTemplate p) (TypeInfo p), [FullTemplate p]) (TypeInfo p)
    alg f = do
        f' <- sequence f
        case f' of
            TemplateF (FullTemplate t i) -> do
                (m, vs) <- State.get
                let k = FullTemplate t i
                case Map.lookup k m of
                    Just t' -> return t'
                    Nothing -> case vs of
                        (t_new:vs') -> do
                            let res = Template (ftId t_new) (ftIndex t_new)
                            State.put (Map.insert k res m, vs')
                            return res
                        [] -> return $ Template (TIdAnonymous 0 (Just "UNKNOWN")) i
            PointerF t | isVoid t -> do
                (_, vs) <- State.get
                case vs of
                    (t_new:vs') -> do
                        State.modify $ \(m, _) -> (m, vs')
                        let applyWrappers (BuiltinType VoidTy) x = x
                            applyWrappers (Const t'') x = Const (applyWrappers t'' x)
                            applyWrappers (Owner t'') x = Owner (applyWrappers t'' x)
                            applyWrappers (Nonnull t'') x = Nonnull (applyWrappers t'' x)
                            applyWrappers (Nullable t'') x = Nullable (applyWrappers t'' x)
                            applyWrappers (Var l t'') x = Var l (applyWrappers t'' x)
                            applyWrappers (Sized t'' l) x = Sized (applyWrappers t'' x) l
                            applyWrappers _ x = x
                        return $ Pointer (applyWrappers t (Template (ftId t_new) (ftIndex t_new)))
                    [] -> return $ Fix f'
            _ -> return $ Fix f'

renameTemplates :: Map (TemplateId 'Global) (TypeInfo 'Global) -> TypeInfo 'Global -> TypeInfo 'Global
renameTemplates m = foldFix $ \case
    TemplateF (FullTemplate t i) ->
        Map.findWithDefault (Template t i) t m
    PointerF (BuiltinType VoidTy) -> Map.findWithDefault (Pointer (BuiltinType VoidTy)) (TIdName "T") m
    f -> Fix f

getDescrTemplates :: TypeDescr p -> [TemplateId p]
getDescrTemplates = \case
    StructDescr _ ts _ _  -> ts
    UnionDescr  _ ts _ _  -> ts
    FuncDescr   _ ts _ _ -> ts
    AliasDescr  _ ts _   -> ts
    _                    -> []


class PhaseOps (p :: Phase) where
    fromGlobalId :: TemplateId 'Global -> TemplateId p
    fromPoly :: Integer -> Int -> Maybe Text -> Origin -> TemplateId p

instance PhaseOps 'Global where
    fromGlobalId = \case
        TIdName n          -> TIdAnonymous 0 (Just n)
        TIdParam i h o     -> TIdParam i h o
        TIdAnonymous i h   -> TIdAnonymous i h
        TIdRec i           -> TIdRec i
    fromPoly _ i h o = TIdParam i h o

instance PhaseOps 'Local where
    fromGlobalId = \case
        TIdName n          -> TIdAnonymous 0 (Just n)
        TIdParam i h o     -> TIdPoly 0 i h o
        TIdAnonymous i h   -> TIdAnonymous i h
        TIdRec i           -> TIdRec i
    fromPoly ph i h o = TIdPoly ph i h o

instantiateDescr :: PhaseOps q => Integer -> Origin -> Map (TemplateId 'Global) (TypeInfo q) -> TypeDescr 'Global -> TypeDescr q
instantiateDescr ph origin m descr =
    case descr of
        StructDescr l _ mems invs ->
            StructDescr l [] (map (second (instantiate ph origin m)) mems) (map (instantiateInvariant ph origin m) invs)
        UnionDescr l _ mems invs ->
            UnionDescr l [] (map (second (instantiate ph origin m)) mems) (map (instantiateInvariant ph origin m) invs)
        FuncDescr l _ ret ps ->
            FuncDescr l [] (instantiate ph origin m ret) (map (instantiate ph origin m) ps)
        AliasDescr l _ ty ->
            AliasDescr l [] (instantiate ph origin m ty)
        IntDescr l std -> IntDescr l std
        EnumDescr l mems -> EnumDescr l (map (instantiate ph origin m) mems)

instantiateInvariant :: PhaseOps q => Integer -> Origin -> Map (TemplateId 'Global) (TypeInfo q) -> Invariant 'Global -> Invariant q
instantiateInvariant ph origin m = \case
    InvCallable f as r -> InvCallable (inst f) (map inst as) (inst r)
    InvEquality t1 t2  -> InvEquality (inst t1) (inst t2)
    InvSubtype t1 t2   -> InvSubtype (inst t1) (inst t2)
    InvCoordinatedPair t1 t2 t3 -> InvCoordinatedPair (inst t1) (inst t2) (inst t3)
  where
    inst = instantiate ph origin m

instantiate :: PhaseOps q => Integer -> Origin -> Map (TemplateId 'Global) (TypeInfo q) -> TypeInfo 'Global -> TypeInfo q
instantiate ph origin m = foldFix alg
  where
    alg f = case f of
        TemplateF (FullTemplate t _) ->
            case Map.lookup t m of
                Just res -> res
                Nothing  -> Fix (bimap convert id f)
        _ -> Fix (bimap convert id f)

    convert :: forall r. PhaseOps r => TemplateId 'Global -> TemplateId r
    convert (TIdName n)        = fromGlobalId $ TIdAnonymous 0 (Just n)
    convert (TIdParam i h o)   = fromPoly ph i h (if origin == TopLevel then o else origin)
    convert (TIdAnonymous i h) = fromGlobalId $ TIdAnonymous i h
    convert (TIdRec i)         = fromGlobalId $ TIdRec i

instantiateGlobal :: Map (TemplateId 'Global) (TypeInfo 'Global) -> TypeInfo 'Global -> TypeInfo 'Global
instantiateGlobal m = foldFix alg
  where
    alg f = case f of
        TemplateF (FullTemplate t _) ->
            case Map.lookup t m of
                Just res -> res
                Nothing  -> Fix f
        _ -> Fix f

toLocal :: Integer -> Origin -> TypeInfo 'Global -> TypeInfo 'Local
toLocal ph origin = instantiate ph origin Map.empty

getTypeParams :: PhaseOps p => TypeSystem -> TypeInfo p -> Maybe [TypeInfo p]
getTypeParams ts ty = case ty of
    Function _ ps -> Just ps
    Pointer t     -> getTypeParams ts t
    Nonnull t     -> getTypeParams ts t
    Nullable t    -> getTypeParams ts t
    Const t       -> getTypeParams ts t
    Var _ t       -> getTypeParams ts t
    TypeRef FuncRef (L _ _ tid) args ->
        case lookupType (templateIdBaseName tid) ts of
            Just descr ->
                let m = Map.fromList (zip (getDescrTemplates descr) args)
                    descr' = instantiateDescr 0 TopLevel m descr
                in case descrToTypeInfo descr' of
                    Function _ ps' -> Just ps'
                    _              -> Nothing
            _ -> Nothing
    TypeRef UnresolvedRef (L _ _ tid) _ ->
        case lookupType (templateIdBaseName tid) ts of
            Just (AliasDescr _ _ t) -> getTypeParams ts (instantiate 0 TopLevel Map.empty t)
            _                       -> Nothing
    _ -> Nothing

toGlobalId :: TemplateId 'Local -> TemplateId 'Global
toGlobalId (TIdInst _ tid)    = tid
toGlobalId (TIdPoly _ i h o)  = TIdParam i h o
toGlobalId (TIdSolver i h)    = TIdParam i h Internal
toGlobalId (TIdAnonymous i h) = TIdAnonymous i h
toGlobalId (TIdRec i)         = TIdRec i

toGlobal :: TypeInfo 'Local -> TypeInfo 'Global
toGlobal = foldFix (Fix . bimap toGlobalId id)

getDescrLexeme :: TypeDescr p -> Lexeme (TemplateId p)
getDescrLexeme = \case
    StructDescr l _ _ _ -> fmap mkId l
    UnionDescr l _ _ _  -> fmap mkId l
    EnumDescr l _ -> fmap mkId l
    IntDescr l _ -> fmap mkId l
    FuncDescr l _ _ _ -> fmap mkId l
    AliasDescr l _ _ -> fmap mkId l

mkId :: Text -> TemplateId p
mkId = TIdAnonymous 0 . Just

resolveRef :: TypeSystem -> TypeInfo 'Global -> TypeInfo 'Global
resolveRef = resolveRefWith Set.empty

resolveRefWith :: Set Text -> TypeSystem -> TypeInfo 'Global -> TypeInfo 'Global
resolveRefWith seen tys ty = go seen ty
  where
    go seen' (TypeRef ref l@(L _ _ tid) args) =
        let name = templateIdBaseName tid in
        case lookupType name tys of
            Nothing -> TypeRef ref l (map (go seen') args)
            Just descr ->
                case descr of
                    AliasDescr _ tps target ->
                        if Set.member name seen'
                        then TypeRef ref l (map (go seen') args)
                        else
                            let args' = if null args && not (null tps)
                                        then [ Template t Nothing | t <- tps ]
                                        else args
                                m = Map.fromList (zip tps (map (go seen') args'))
                            in go (Set.insert name seen') (instantiateGlobal m target)
                    _ ->
                        let ref' = case descr of
                                    StructDescr{} -> StructRef
                                    UnionDescr{}  -> UnionRef
                                    EnumDescr{}   -> EnumRef
                                    IntDescr{}    -> IntRef
                                    FuncDescr{}   -> FuncRef
                            tps = getDescrTemplates descr
                            args' = if null args && not (null tps)
                                    then [ Template t Nothing | t <- tps ]
                                    else args
                            l' = getDescrLexeme descr
                        in TypeRef ref' l' (map (go (Set.insert name seen')) args')
    go seen' (Fix f) = Fix (fmap (go seen') f)

resolveRefLocal :: TypeSystem -> TypeInfo 'Local -> TypeInfo 'Local
resolveRefLocal tys ty = go Set.empty ty
  where
    go seen (TypeRef ref l@(L _ _ tid) args) =
        let name = templateIdBaseName tid in
        if Set.member name seen
        then TypeRef ref l (map (go seen) args)
        else case lookupType name tys of
            Nothing -> TypeRef ref l (map (go seen) args)
            Just descr ->
                let tps = getDescrTemplates descr
                    args' = if null args && not (null tps)
                            then [ instantiate 0 TopLevel (Map.fromList (zip tps args)) (Template t Nothing) | t <- tps ]
                            else args
                    descr' = instantiateDescr 0 TopLevel (Map.fromList (zip tps args')) descr
                in case descr' of
                    AliasDescr _ _ target ->
                        go (Set.insert name seen) target
                    _ ->
                        let ref' = case descr' of
                                    StructDescr{} -> StructRef
                                    UnionDescr{}  -> UnionRef
                                    EnumDescr{}   -> EnumRef
                                    IntDescr{}    -> IntRef
                                    FuncDescr{}   -> FuncRef
                            l' = getDescrLexeme descr'
                        in TypeRef ref' l' (map (go seen) args')
    go seen (Fix f) = Fix (fmap (go seen) f)

setOrigin :: Origin -> TypeInfo p -> TypeInfo p
setOrigin o = foldFix $ \case
    TemplateF (FullTemplate tid idx) -> Template (setOriginId o tid) idx
    f -> Fix f

setOriginId :: Origin -> TemplateId p -> TemplateId p
setOriginId o = \case
    TIdPoly ph i h _ -> TIdPoly ph i h o
    TIdParam i h _   -> TIdParam i h o
    tid              -> tid

getBaseOrigin :: Origin -> Origin
getBaseOrigin (MemberOrigin o _) = getBaseOrigin o
getBaseOrigin (ArrayOrigin o _)  = getBaseOrigin o
getBaseOrigin o                  = o

getOriginLineage :: Origin -> [Origin]
getOriginLineage (MemberOrigin o f) = MemberOrigin o f : getOriginLineage o
getOriginLineage (ArrayOrigin o i)  = ArrayOrigin o i : getOriginLineage o
getOriginLineage o                  = [o]

indexTemplates :: TypeInfo p -> TypeInfo p -> TypeInfo p
indexTemplates idx = mapTemplates (\(FullTemplate t _) -> Template t (Just idx))

mapTemplates :: (FullTemplate p -> TypeInfo p) -> TypeInfo p -> TypeInfo p
mapTemplates f = foldFix $ \case
    TemplateF ft -> f ft
    f'           -> Fix f'

isInt :: StdType -> Bool
isInt = \case
    CharTy   -> True
    U08Ty    -> True
    S08Ty    -> True
    U16Ty    -> True
    S16Ty    -> True
    U32Ty    -> True
    S32Ty    -> True
    U64Ty    -> True
    S64Ty    -> True
    SizeTy   -> True
    NullPtrTy -> False
    _        -> False

unwrap :: TypeInfo p -> TypeInfo p
unwrap (Const t)    = unwrap t
unwrap (Owner t)    = unwrap t
unwrap (Nonnull t)  = unwrap t
unwrap (Nullable t) = unwrap t
unwrap (Sized t _)  = unwrap t
unwrap (Var _ t)    = unwrap t
unwrap t            = t

stripAllWrappers :: TypeInfo p -> TypeInfo p
stripAllWrappers (Pointer t)        = stripAllWrappers t
stripAllWrappers (Array (Just t) _) = stripAllWrappers t
stripAllWrappers (Nonnull t)        = stripAllWrappers t
stripAllWrappers (Nullable t)       = stripAllWrappers t
stripAllWrappers (Const t)          = stripAllWrappers t
stripAllWrappers (Owner t)          = stripAllWrappers t
stripAllWrappers (Sized t _)        = stripAllWrappers t
stripAllWrappers (Var _ t)          = stripAllWrappers t
stripAllWrappers t                  = t

isPointerLike :: TypeInfo p -> Bool
isPointerLike = foldFix $ \case
    PointerF _ -> True
    ArrayF _ _ -> True
    QualifiedF _ t -> t
    VarF _ t -> t
    SizedF t _ -> t
    _ -> False

getInnerType :: TypeInfo p -> TypeInfo p
getInnerType t = case unwrap t of
    Pointer inner        -> inner
    Array (Just inner) _ -> inner
    _                    -> t

promoteNonnull :: TypeInfo p -> TypeInfo p
promoteNonnull = foldFix $ \case
    QualifiedF qs t -> Qualified (Set.insert QNonnull (Set.delete QNullable qs)) t
    f           -> Fix f

descrToTypeInfo :: TypeDescr p -> TypeInfo p
descrToTypeInfo = \case
    StructDescr l args _ _ -> TypeRef StructRef (fmap mkId l) (map (\t -> Template t Nothing) args)
    UnionDescr l args _ _  -> TypeRef UnionRef (fmap mkId l) (map (\t -> Template t Nothing) args)
    EnumDescr l _        -> TypeRef EnumRef (fmap mkId l) []
    IntDescr l _         -> TypeRef IntRef (fmap mkId l) []
    FuncDescr l args r p ->
        let sig = Function r p
        in if null args then sig else TypeRef FuncRef (fmap mkId l) (map (\t -> Template t Nothing) args)
    AliasDescr l args t  -> if null args then t else TypeRef UnresolvedRef (fmap mkId l) (map (\arg -> Template arg Nothing) args)

isVarArg :: TypeInfo p -> Bool
isVarArg VarArg = True
isVarArg _      = False

isSpecial :: TypeInfo p -> Bool
isSpecial = foldFix $ \case
    VarArgF             -> True
    BuiltinTypeF VoidTy -> True
    QualifiedF _ t      -> t
    VarF _ t            -> t
    SizedF t _          -> t
    _                   -> False

promote :: TypeInfo p -> TypeInfo p -> TypeInfo p
promote t1 t2                 | t1 == t2 = t1
promote (BuiltinType F64Ty) _ = BuiltinType F64Ty
promote _ (BuiltinType F64Ty) = BuiltinType F64Ty
promote (BuiltinType F32Ty) _ = BuiltinType F32Ty
promote _ (BuiltinType F32Ty) = BuiltinType F32Ty
promote (BuiltinType S64Ty) _ = BuiltinType S64Ty
promote _ (BuiltinType S64Ty) = BuiltinType S64Ty
promote (BuiltinType U64Ty) _ = BuiltinType U64Ty
promote _ (BuiltinType U64Ty) = BuiltinType U64Ty
promote t _                   = t

isSockaddr :: TypeInfo p -> Bool
isSockaddr t = case unwrap t of
    TypeRef ref (L _ _ tid) _ -> templateIdBaseName tid == "sockaddr" && (ref == StructRef || ref == UnresolvedRef)
    _ -> False

isSockaddrIn :: TypeInfo p -> Bool
isSockaddrIn t = case unwrap t of
    TypeRef ref (L _ _ tid) _ -> templateIdBaseName tid == "sockaddr_in" && (ref == StructRef || ref == UnresolvedRef)
    _ -> False

isSockaddrIn6 :: TypeInfo p -> Bool
isSockaddrIn6 t = case unwrap t of
    TypeRef ref (L _ _ tid) _ -> templateIdBaseName tid == "sockaddr_in6" && (ref == StructRef || ref == UnresolvedRef)
    _ -> False

isSockaddrStorage :: TypeInfo p -> Bool
isSockaddrStorage t = case unwrap t of
    TypeRef ref (L _ _ tid) _ -> templateIdBaseName tid == "sockaddr_storage" && (ref == StructRef || ref == UnresolvedRef)
    _ -> False

isNetworkingStruct :: TypeInfo p -> Bool
isNetworkingStruct t = isSockaddr t || isSockaddrIn t || isSockaddrIn6 t || isSockaddrStorage t

isAnyStruct :: TypeInfo p -> Bool
isAnyStruct t = case unwrap t of
    TypeRef StructRef _ _     -> True
    TypeRef UnresolvedRef _ _ -> True
    _                         -> False

getTypeLexeme :: TypeInfo p -> Maybe (Lexeme Text)
getTypeLexeme = \case
    TypeRef _ l _    -> Just (fmap templateIdBaseName l)
    Pointer t        -> getTypeLexeme t
    Sized _ l        -> Just (fmap templateIdBaseName l)
    Const t          -> getTypeLexeme t
    Owner t          -> getTypeLexeme t
    Nonnull t        -> getTypeLexeme t
    Nullable t       -> getTypeLexeme t
    ExternalType l   -> Just (fmap templateIdBaseName l)
    Array (Just t) _ -> getTypeLexeme t
    Var l _          -> Just (fmap templateIdBaseName l)
    Function r _     -> getTypeLexeme r
    IntLit l         -> Just (fmap templateIdBaseName l)
    NameLit l        -> Just (fmap templateIdBaseName l)
    EnumMem l        -> Just (fmap templateIdBaseName l)
    _                -> Nothing

isLPSTR :: TypeInfo p -> Bool
isLPSTR t = case unwrap t of
    TypeRef _ (L _ _ tid) _ -> templateIdBaseName tid == "LPSTR" || templateIdBaseName tid == "lpstr"
    _                        -> False

isPointerToChar :: TypeInfo p -> Bool
isPointerToChar t = case unwrap t of
    Pointer t' -> case unwrap t' of
        BuiltinType CharTy -> True
        _                  -> False
    _          -> False

containsTemplate :: TypeInfo p -> Bool
containsTemplate = foldFix $ \case
    TemplateF _ -> True
    f           -> any id f

isGeneric :: TypeInfo p -> Bool
isGeneric t = fst $ foldFix alg t
  where
    alg = \case
        TemplateF _ -> (True, False)
        QualifiedF qs (_, _) | QOwner `Set.member` qs -> (True, False)
        BuiltinTypeF VoidTy -> (False, True)
        PointerF (isG, isV) -> (isG || isV, False)
        ArrayF m _ -> (fromMaybe False (fmap fst m), False)
        f -> (any fst f, False)

resolveType' :: TypeInfo p -> TypeInfo p
resolveType' (Var _ t)    = resolveType' t
resolveType' (Nonnull t)  = resolveType' t
resolveType' (Nullable t) = resolveType' t
resolveType' (Const t)    = resolveType' t
resolveType' (Owner t)    = resolveType' t
resolveType' (Sized t _)  = resolveType' t
resolveType' t            = t

lookupMemberType :: Text -> TypeDescr p -> Maybe (TypeInfo p)
lookupMemberType field = \case
    StructDescr _ _ members _ -> lookupIn members
    UnionDescr  _ _ members _ -> lookupIn members
    _                       -> Nothing
  where
    lookupIn ms = lookup field [ (C.lexemeText l, t) | (l, t) <- ms ]

typeDescrToType :: TypeDescr p -> TypeInfo p
typeDescrToType = \case
    StructDescr l args _ _  -> TypeRef StructRef (fmap mkId l) (map (\t -> Template t Nothing) args)
    UnionDescr l args _ _   -> TypeRef UnionRef (fmap mkId l) (map (\t -> Template t Nothing) args)
    AliasDescr l args _     -> TypeRef UnresolvedRef (fmap mkId l) (map (\t -> Template t Nothing) args)
    FuncDescr l args _ _    -> TypeRef FuncRef (fmap mkId l) (map (\t -> Template t Nothing) args)
    IntDescr _ std          -> BuiltinType std
    EnumDescr l _           -> TypeRef EnumRef (fmap mkId l) []

