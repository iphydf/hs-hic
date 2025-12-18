{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Inference.Engine
    ( inferProgram
    ) where

import           Control.Monad                             (foldM)
import           Control.Monad.State.Strict                (State, evalState)
import           Data.Fix                                  (Fix (..), hoistFix)
import           Data.List                                 (foldl')
import           Data.Map.Strict                           (Map)
import qualified Data.Map.Strict                           as Map
import           Data.Text                                 (Text)
import qualified Language.Cimple                           as C
import qualified Language.Cimple.Program                   as Program
import           Language.Hic.Ast                          (Node, NodeF (..))
import           Language.Hic.Inference.Context            (Context,
                                                            collectContext)
import           Language.Hic.Inference.Feature            (Feature (..))
import qualified Language.Hic.Inference.Passes.Iteration   as Iteration
import qualified Language.Hic.Inference.Passes.Raise       as Raise
import qualified Language.Hic.Inference.Passes.Scoped      as Scoped
import qualified Language.Hic.Inference.Passes.TaggedUnion as TaggedUnion
import           Language.Hic.Inference.Program.Types      (Program (..))

-- | Global inference over an entire Program.
inferProgram :: Program.Program Text -> (Map FilePath [Node (C.Lexeme Text)], [Text])
inferProgram cprog =
    let initialCtx = collectContext cprog
        wrapNode = hoistFix CimpleNode
        initialProg :: Program (C.Lexeme Text) = Program
            { progAsts = Map.fromList [ (f, map wrapNode ns) | (f, ns) <- Program.toList cprog ]
            , progDiagnostics = []
            }

        features = [TaggedUnion.feature, Scoped.feature, Raise.feature, Iteration.feature]

        (finalProg, finalCtx) = fixpoint features initialCtx initialProg

        diags = concatMap (\f -> featureValidate f finalCtx finalProg) features
    in (progAsts finalProg, diags)

-- | Runs the Gather and Infer phases for all features.
-- We use a fixed number of passes (3) to ensure guaranteed termination while
-- allowing enough iterations for feature interactions (e.g., TaggedUnion -> Iteration).
fixpoint :: [Feature] -> Context -> Program (C.Lexeme Text) -> (Program (C.Lexeme Text), Context)
fixpoint features ctx prog =
    foldl' (\(p, c) _ -> onePass p c) (prog, ctx) [1..3 :: Int]
  where
    onePass p c =
        let c' = foldl' (\acc f -> featureGather f p acc) c features
            p' = evalState (inferAll features c' p) False
        in (p', c')

inferAll :: [Feature] -> Context -> Program (C.Lexeme Text) -> State Bool (Program (C.Lexeme Text))
inferAll features ctx prog = do
    newAsts <- mapM (inferFile features ctx) (Map.toList (progAsts prog))
    return $ prog { progAsts = Map.fromList newAsts }

inferFile :: [Feature] -> Context -> (FilePath, [Node (C.Lexeme Text)]) -> State Bool (FilePath, [Node (C.Lexeme Text)])
inferFile features ctx (file, nodes) = do
    newNodes <- mapM (inferNode features ctx file) nodes
    return (file, newNodes)

inferNode :: [Feature] -> Context -> FilePath -> Node (C.Lexeme Text) -> State Bool (Node (C.Lexeme Text))
inferNode features ctx file node =
    foldM (\n f -> featureInfer f ctx file n) node features
