{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Language.Hic.Inference
    ( lower
    ) where

import           Data.Fix                                  (Fix (..), foldFix)
import           Data.Maybe                                (listToMaybe,
                                                            mapMaybe)
import qualified Language.Cimple                           as C
import           Language.Hic.Ast
import           Language.Hic.Inference.Feature            (featureLower)
import qualified Language.Hic.Inference.Passes.Iteration   as Iteration
import qualified Language.Hic.Inference.Passes.Raise       as Raise
import qualified Language.Hic.Inference.Passes.Scoped      as Scoped
import qualified Language.Hic.Inference.Passes.TaggedUnion as TaggedUnion

-- | Lowers a Hic AST back to a standard Cimple AST.
lower :: Node lexeme -> C.Node lexeme
lower = foldFix $ \case
    CimpleNode f -> Fix f
    HicNode h    -> lowerHic h

lowerHic :: HicNode lexeme (C.Node lexeme) -> C.Node lexeme
lowerHic h =
    let features = [TaggedUnion.feature, Scoped.feature, Raise.feature, Iteration.feature]
        applyLower f = featureLower f h
    in case listToMaybe $ mapMaybe applyLower features of
        Just n  -> n
        Nothing -> error "lowerHic: No feature could lower this node"
