{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.Inference.Passes.Type
    ( getType
    ) where

import           Data.Fix                          (foldFix)
import           Data.Map.Strict                   (Map)
import qualified Data.Map.Strict                   as Map
import           Data.Text                         (Text)
import qualified Language.Cimple                   as C
import           Language.Hic.Core.TypeSystem      (TypeDescr (..), TypeInfo,
                                                    pattern TypeRef)
import qualified Language.Hic.TypeSystem.Core.Base as TS

import           Language.Hic.Ast                  (Node, NodeF (CimpleNode))
import qualified Language.Hic.Ast                  as H
import           Language.Hic.Inference.Context    (Context (..))
import           Language.Hic.Inference.Utils      (getTypeInfoName,
                                                    resolveTypedef)

getType :: Context -> Map Text Text -> Node (C.Lexeme Text) -> Maybe Text
getType ctx env = foldFix $ \case
    CimpleNode node -> case node of
        C.VarExpr l -> do
            let name = C.lexemeText l
            case Map.lookup name env of
                Just tyName -> Just $ resolveTypedef ctx tyName
                Nothing ->
                    -- Fallback to TypeSystem if not in env
                    case TS.lookupType name (ctxTypeSystem ctx) of
                        Just (AliasDescr _ _ target) -> getTypeInfoName target
                        _                            -> Nothing
        C.PointerAccess mTyName field -> do
            tyName <- mTyName
            case TS.lookupType tyName (ctxTypeSystem ctx) of
                Just descr | Just mTy <- TS.lookupMemberType (C.lexemeText field) descr ->
                    getTypeInfoName mTy
                _ -> do
                    -- Fallback to old heuristic
                    fields <- Map.lookup tyName (ctxUnions ctx)
                    if C.lexemeText field `elem` fields
                        then Just "union member"
                        else Nothing
        C.MemberAccess mTyName field -> do
            tyName <- mTyName
            case TS.lookupType tyName (ctxTypeSystem ctx) of
                Just descr | Just mTy <- TS.lookupMemberType (C.lexemeText field) descr ->
                    getTypeInfoName mTy
                _ -> do
                    fields <- Map.lookup tyName (ctxUnions ctx)
                    if C.lexemeText field `elem` fields
                        then Just "union member"
                        else Nothing
        C.ArrayAccess base _ -> base
        C.ParenExpr e -> e
        _ -> Nothing
    H.HicNode node -> case node of
        H.IterationElement _ container -> container
        _                              -> Nothing
