{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Language.Hic.InferenceSpec where

import           Data.Fix                (Fix (..), unFix)
import           Data.Text               (Text)
import           Test.Hspec              (Spec, describe, it, shouldBe)

import qualified Language.Cimple         as C
import qualified Language.Cimple.Program as C
import           Language.Hic.Ast
import           Language.Hic.Inference

spec :: Spec
spec = do
    let dummyLoc = C.AlexPn 0 0 0
    let lVar v = C.L dummyLoc C.IdVar v
    let lInt i = C.L dummyLoc C.LitInteger i

    describe "lower" $ do
        let liftHic :: C.Node (C.Lexeme Text) -> Node (C.Lexeme Text)
            liftHic (Fix f) = Fix (CimpleNode (fmap liftHic f))

        it "lowers a CimpleNode" $ do
            let node = Fix (CimpleNode (C.Break)) :: Node (C.Lexeme Text)
            lower node `shouldBe` (Fix C.Break :: C.Node (C.Lexeme Text))

        it "lowers a Raise node" $ do
            let var = Fix (C.VarExpr (lVar "error_var"))
            let val = Fix (C.LiteralExpr C.Int (lInt "1"))
            let err = Fix (C.LiteralExpr C.Int (lInt "-1"))
            let node = Fix (HicNode (Raise (Just (liftHic var)) (liftHic val) (ReturnError (liftHic err))))
            lower node `shouldBe` (Fix (C.Group
                [ Fix (C.ExprStmt (Fix (C.AssignExpr var C.AopEq val)))
                , Fix (C.Return (Just err))
                ]) :: C.Node (C.Lexeme Text))
