{-# LANGUAGE RankNTypes #-}
module Language.Hic.Inference.Feature
    ( Feature (..)
    ) where

import           Control.Monad.State.Strict           (State)
import           Data.Text                            (Text)
import qualified Language.Cimple                      as C
import           Language.Hic.Ast                     (HicNode, Node)
import           Language.Hic.Inference.Context       (Context)
import           Language.Hic.Inference.Program.Types (Program)

data Feature = Feature
    { featureName     :: Text
    -- | Phase 1: Gather global context.
    -- Runs in the fixpoint loop.
    , featureGather   :: Program (C.Lexeme Text) -> Context -> Context

    -- | Phase 2: Infer high-level constructs.
    -- Runs in the fixpoint loop. Returns True if changes were made.
    , featureInfer    :: Context -> FilePath -> Node (C.Lexeme Text) -> State Bool (Node (C.Lexeme Text))

    -- | Phase 3: Validate invariants after inference is complete.
    , featureValidate :: Context -> Program (C.Lexeme Text) -> [Text]

    -- | Lowering: Convert high-level constructs back to Cimple.
    , featureLower    :: forall l. HicNode l (C.Node l) -> Maybe (C.Node l)
    }
