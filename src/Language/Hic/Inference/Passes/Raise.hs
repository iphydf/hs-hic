{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Inference.Passes.Raise
    ( feature
    ) where

import           Control.Monad.State.Strict     (State, modify)
import qualified Control.Monad.State.Strict     as State
import           Data.Fix                       (Fix (..), foldFix, foldFixM)
import           Data.Text                      (Text)
import qualified Language.Cimple                as C
import           Language.Hic.Ast               (HicNode (..), Node, NodeF (..),
                                                 ReturnIntent (..))
import           Language.Hic.Inference.Context (Context)
import           Language.Hic.Inference.Feature (Feature (..))

feature :: Feature
feature = Feature
    { featureName     = "Raise"
    , featureGather   = \_ ctx -> ctx
    , featureInfer    = infer
    , featureValidate = \_ _ -> []
    , featureLower    = lower
    }

data ErrorValueInfo = IsLiteral Text | OtherValue | IsErrorValue

infer :: Context -> FilePath -> Node (C.Lexeme Text) -> State Bool (Node (C.Lexeme Text))
infer _ctx _file = foldFixM alg
  where
    alg (CimpleNode (C.CompoundStmt stmts)) =
        Fix . CimpleNode . C.CompoundStmt <$> inferRaise stmts
    alg f = return $ Fix f

    inferRaise [] = return []
    inferRaise (s1 : s2 : ss)
        | Just (out, val) <- matchAssign s1
        , Just ret <- matchReturn s2
        , isErrorValue ret = do
            State.modify (const True)
            let res = Fix $ HicNode $ Raise (Just out) val (ReturnError ret)
            (res :) <$> inferRaise ss
    inferRaise (s : ss) = (s :) <$> inferRaise ss

    matchAssign :: Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text), Node (C.Lexeme Text))
    matchAssign n = case unFix n of
        CimpleNode (C.ExprStmt e) -> case unFix e of
            CimpleNode (C.AssignExpr lhs C.AopEq val) -> Just (lhs, val)
            _                                         -> Nothing
        _ -> Nothing

    matchReturn :: Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text))
    matchReturn n = case unFix n of
        CimpleNode (C.Return (Just e)) -> Just e
        _                              -> Nothing

    isErrorValue :: Node (C.Lexeme Text) -> Bool
    isErrorValue node = case foldFix alg' node of
        IsErrorValue -> True
        _            -> False
      where
        alg' (CimpleNode (C.LiteralExpr C.Int l))
            | C.lexemeText l == "1" = IsErrorValue -- Could be literal 1 or error value
            | C.lexemeText l == "-1" = IsErrorValue
            | otherwise = IsLiteral (C.lexemeText l)
        alg' (CimpleNode (C.UnaryExpr C.UopMinus inner)) =
            case inner of
                IsLiteral "1" -> IsErrorValue
                IsErrorValue  -> IsErrorValue -- Handle -1 if 1 was already IsErrorValue
                _             -> OtherValue
        alg' (CimpleNode (C.LiteralExpr C.ConstId l))
            | C.lexemeText l == "nullptr" = IsErrorValue
        alg' (CimpleNode (C.LiteralExpr C.Bool l))
            | C.lexemeText l == "false" = IsErrorValue
        alg' _ = OtherValue

lower :: HicNode l (C.Node l) -> Maybe (C.Node l)
lower (Raise maybeOut val ret) =
    Just $ Fix $ C.Group $
        maybe [] (\out -> [Fix $ C.ExprStmt (Fix $ C.AssignExpr out C.AopEq val)]) maybeOut
        ++ [lowerReturn ret]
  where
    lowerReturn ReturnVoid      = Fix $ C.Return Nothing
    lowerReturn (ReturnValue v) = Fix $ C.Return (Just v)
    lowerReturn (ReturnError e) = Fix $ C.Return (Just e)
lower _ = Nothing
