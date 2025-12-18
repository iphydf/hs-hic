{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Ordered.NullabilitySpec where

import           Control.Applicative                         ((<|>))
import           Control.Monad.Identity                      (Identity (..))
import           Data.Fix                                    (Fix (..))
import           Data.Foldable                               (toList)
import           Data.List                                   (foldl')
import           Data.Map.Strict                             (Map)
import qualified Data.Map.Strict                             as Map
import           Data.Maybe                                  (fromJust,
                                                              fromMaybe)
import           Data.Set                                    (Set)
import qualified Data.Set                                    as Set
import           Data.Text                                   (Text)
import qualified Data.Text                                   as T
import qualified Language.Cimple                             as C
import qualified Language.Cimple.Program                     as Program
import           Language.Hic.Core.AstUtils                  (getAlexPosn)
import           Language.Hic.TestUtils                      (mustParse,
                                                              mustParseNodes)
import           Language.Hic.TypeSystem.Ordered.Nullability
import           Test.Hspec

firstNode :: Program.Program Text -> C.Node (C.Lexeme Text)
firstNode prog = case Program.toList prog of
    ((_, n:_):_) -> n
    _            -> error "firstNode: empty program"

findInProgram :: (C.Node (C.Lexeme Text) -> Bool) -> Program.Program Text -> C.Node (C.Lexeme Text)
findInProgram p prog = fromMaybe (error "node not found") $
    foldl' (\acc (_, nodes) -> acc <|> foldl' (\acc' n -> acc' <|> findNodeMaybe p n) Nothing nodes) Nothing (Program.toList prog)

findNodeMaybe :: (C.Node (C.Lexeme Text) -> Bool) -> C.Node (C.Lexeme Text) -> Maybe (C.Node (C.Lexeme Text))
findNodeMaybe p n@(Fix f)
    | p n = Just n
    | otherwise = foldl' (\acc c -> acc <|> findNodeMaybe p c) Nothing (toList f)

spec :: Spec
spec = do
    let isDecl name = \case
            Fix (C.VarDeclStmt (Fix (C.VarDecl _ (C.L _ _ n) _)) _) -> n == name
            _ -> False

    it "identifies non-null variables after a direct check" $ do
        let code = [ "void f(int *p) {"
                   , "  if (p) {"
                   , "    int x = 0;"
                   , "  }"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p"])

    it "identifies non-null variables after a != nullptr check" $ do
        let code = [ "void f(int *p) {"
                   , "  if (p != nullptr) {"
                   , "    int x = 0;"
                   , "  }"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p"])

    it "identifies non-null variables in the else branch after a == nullptr check" $ do
        let code = [ "void f(int *p) {"
                   , "  if (p == nullptr) {"
                   , "    return;"
                   , "  }"
                   , "  int x = 0;"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p"])

    it "joins non-null information correctly (soundness)" $ do
        let code = [ "void f(int *p, int *q) {"
                   , "  if (p) {"
                   , "    p = nullptr; /* p is non-null here, but we kill it */"
                   , "  } else {"
                   , "    q = nullptr; /* nothing known */"
                   , "  }"
                   , "  int x = 0;"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just Set.empty

    it "tracks non-nullness through assignments" $ do
        let code = [ "void f(int *p) {"
                   , "  int *q = nullptr;"
                   , "  if (p) {"
                   , "    q = p;"
                   , "    int x = 0;"
                   , "  }"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p", "q"])

    it "identifies non-null variables after dereference" $ do
        let code = [ "void f(int *p) {"
                   , "  *p = 1;"
                   , "  int x = 0;"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p"])

    it "identifies non-null variables after member access" $ do
        let code = [ "struct My_Struct { int f; };"
                   , "void f(struct My_Struct *p) {"
                   , "  p->f = 1;"
                   , "  int x = 0;"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p"])

    it "identifies non-null variables after array access" $ do
        let code = [ "void f(int *p) {"
                   , "  p[0] = 1;"
                   , "  int x = 0;"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p"])

    it "identifies non-null variables in logical AND" $ do
        let code = [ "void f(int *p, int *q) {"
                   , "  if (p && q) {"
                   , "    int x = 0;"
                   , "  }"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p", "q"])

    it "recognizes 0 as a null constant" $ do
        let code = [ "void f(int *p) {"
                   , "  if (p != 0) {"
                   , "    int x = 0;"
                   , "  }"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p"])

    it "treats explicit cast to non-null as an assertion" $ do
        let code = [ "void f(int *p) {"
                   , "  int *other_p = (int * _Nonnull)p;"
                   , "  int x = 0;"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["other_p", "p"])

    it "refines nullability after call to function with _Nonnull parameter" $ do
        let code = [ "void g(int * _Nonnull p);"
                   , "void f(int *p) {"
                   , "  g(p);"
                   , "  int x = 0;"
                   , "}"
                   ]
        prog <- mustParse code
        let result = runNullabilityAnalysis prog
        let facts = fromJust $ Map.lookup "f" (nrStatementFacts result)
        let pos = fromJust $ getAlexPosn (findInProgram (isDecl "x") prog)
        Map.lookup pos facts `shouldBe` Just (Set.fromList ["p"])
