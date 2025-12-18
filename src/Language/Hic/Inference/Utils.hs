{-# LANGUAGE LambdaCase #-}
module Language.Hic.Inference.Utils
    ( getTypeName
    , dummyLexeme
    , matchAccess
    , getTypeInfoName
    , resolveTypedef
    ) where

import           Data.Fix                          (Fix (..), foldFix)
import           Data.Text                         (Text)
import qualified Language.Cimple                   as C
import           Language.Hic.Ast                  (Node, NodeF (..))
import           Language.Hic.Core.TypeSystem      (TypeDescr (..), TypeInfo,
                                                    TypeInfoF (..))
import           Language.Hic.Inference.Context    (Context (..))
import qualified Language.Hic.TypeSystem.Core.Base as TS

getTypeName :: Node (C.Lexeme Text) -> Maybe Text
getTypeName = foldFix $ \case
    CimpleNode (C.TyUserDefined l) -> Just (C.lexemeText l)
    CimpleNode (C.TyStruct l)      -> Just (C.lexemeText l)
    CimpleNode (C.TyUnion l)       -> Just (C.lexemeText l)
    CimpleNode (C.TyStd l)         -> Just (C.lexemeText l)
    CimpleNode (C.TyPointer ty)    -> ty
    CimpleNode (C.TyConst ty)      -> ty
    CimpleNode (C.TyNonnull ty)    -> ty
    CimpleNode (C.TyNullable ty)   -> ty
    CimpleNode (C.TyOwner ty)      -> ty
    CimpleNode (C.TyBitwise ty)    -> ty
    _                              -> Nothing

dummyLexeme :: Text -> C.Lexeme Text
dummyLexeme t = C.L (C.AlexPn 0 0 0) C.IdVar t

matchAccess :: Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text), Bool, C.Lexeme Text)
matchAccess (Fix (CimpleNode (C.PointerAccess obj field))) = Just (obj, True, field)
matchAccess (Fix (CimpleNode (C.MemberAccess obj field)))  = Just (obj, False, field)
matchAccess _                                              = Nothing

getTypeInfoName :: TypeInfo p -> Maybe Text
getTypeInfoName = foldFix $ \case
    TypeRefF _ (C.L _ _ tid) _ -> Just (TS.templateIdToText tid)
    PointerF t                 -> t
    QualifiedF _ t             -> t
    _                          -> Nothing

resolveTypedef :: Context -> Text -> Text
resolveTypedef c n =
    case TS.lookupType n (ctxTypeSystem c) of
        Just (AliasDescr _ _ target) ->
            case getTypeInfoName target of
                Just next -> if next == n then n else resolveTypedef c next
                Nothing   -> n
        _ -> n
