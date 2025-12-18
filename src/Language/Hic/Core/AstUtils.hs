{-# LANGUAGE LambdaCase #-}
module Language.Hic.Core.AstUtils
    ( getLexeme
    , getAlexPosn
    , isLvalue
    , parseInteger
    , readHex
    , isNonnullType
    , isNonnullParam
    , isExpression
    , getVar
    , getParamName
    ) where

import           Control.Applicative ((<|>))
import           Control.Monad       (join)
import           Data.Char           (digitToInt)
import           Data.Fix            (Fix (..), foldFix)
import           Data.Foldable       (toList)
import           Data.List           (find)
import           Data.Maybe          (isJust)
import           Data.Text           (Text)
import qualified Data.Text           as T
import           Language.Cimple     (AlexPosn (..), Lexeme (..))
import qualified Language.Cimple     as C

getAlexPosn :: C.Node (C.Lexeme l) -> Maybe AlexPosn
getAlexPosn node = case getLexeme node of
    Just (C.L pos _ _) -> Just pos
    Nothing            -> Nothing

getLexeme :: C.Node (C.Lexeme l) -> Maybe (C.Lexeme l)
getLexeme = foldFix $ \case
    C.VarExpr l               -> Just l
    C.LiteralExpr _ l         -> Just l
    C.VarDecl _ l _           -> Just l
    C.MemberAccess _ l        -> Just l
    C.PointerAccess _ l       -> Just l
    C.FunctionPrototype _ l _ -> Just l
    C.CallbackDecl _ l        -> Just l
    C.ConstDecl _ l           -> Just l
    C.ConstDefn _ _ l _       -> Just l
    C.Typedef _ l _           -> Just l
    C.Struct l _              -> Just l
    C.Union l _               -> Just l
    C.EnumDecl l _ _          -> Just l
    C.Enumerator l _          -> Just l
    C.UnaryExpr _ e           -> e
    C.BinaryExpr e _ _        -> e
    C.CastExpr _ e            -> e
    C.ParenExpr e             -> e
    C.ArrayAccess e _         -> e
    C.FunctionCall e _        -> e
    C.AssignExpr e _ _        -> e
    C.TernaryExpr c _ _       -> c
    C.SizeofExpr e            -> e
    C.CompoundLiteral _ e     -> e
    C.InitialiserList es      -> join (find isJust es)
    C.VarDeclStmt decl mInit  -> decl <|> join mInit
    C.ExprStmt e              -> e
    C.FunctionDefn _ proto _  -> proto
    C.Label _ stmt            -> stmt
    C.MacroBodyStmt stmt      -> stmt
    _                         -> Nothing

isLvalue :: C.Node (C.Lexeme l) -> Bool
isLvalue = foldFix $ \case
    C.VarExpr _              -> True
    C.MemberAccess _ _       -> True
    C.PointerAccess _ _      -> True
    C.ArrayAccess _ _        -> True
    C.UnaryExpr C.UopDeref _ -> True
    C.ParenExpr e            -> e
    _                        -> False

parseInteger :: Text -> Maybe Integer
parseInteger val =
    case T.unpack val of
        ('0':'x':xs) -> Just (fromIntegral $ readHex xs)
        xs -> case reads xs of
            [(n, "")] -> Just n
            _         -> Nothing

readHex :: String -> Integer
readHex xs = foldl (\acc x -> acc * 16 + fromIntegral (digitToInt x)) (0 :: Integer) xs

isNonnullType :: C.Node (C.Lexeme Text) -> Bool
isNonnullType = foldFix $ \case
    C.TyNonnull _ -> True
    f              -> any id f

isNonnullParam :: C.Node (C.Lexeme Text) -> Bool
isNonnullParam (Fix (C.VarDecl ty _ _)) = isNonnullType ty
isNonnullParam (Fix (C.NonNullParam _)) = True
isNonnullParam (Fix (C.Commented _ p))  = isNonnullParam p
isNonnullParam _                        = False

isExpression :: C.NodeF lexeme a -> Bool
isExpression = \case
    C.InitialiserList {} -> True
    C.UnaryExpr {}       -> True
    C.BinaryExpr {}      -> True
    C.TernaryExpr {}     -> True
    C.AssignExpr {}      -> True
    C.ParenExpr {}       -> True
    C.CastExpr {}        -> True
    C.CompoundLiteral {} -> True
    C.SizeofExpr {}      -> True
    C.SizeofType {}      -> True
    C.LiteralExpr {}     -> True
    C.VarExpr {}         -> True
    C.MemberAccess {}    -> True
    C.PointerAccess {}   -> True
    C.ArrayAccess {}     -> True
    C.FunctionCall {}    -> True
    C.CommentExpr {}     -> True
    _                    -> False

getVar :: C.Node (C.Lexeme Text) -> Maybe Text
getVar (Fix (C.VarExpr (C.L _ _ name))) = Just name
getVar (Fix (C.ParenExpr e))            = getVar e
getVar _                                = Nothing

getParamName :: C.Node (C.Lexeme Text) -> Maybe Text
getParamName (Fix (C.VarDecl _ (C.L _ _ name) _)) = Just name
getParamName (Fix (C.NonNullParam n))             = getParamName n
getParamName (Fix (C.Commented _ n))              = getParamName n
getParamName _                                    = Nothing

