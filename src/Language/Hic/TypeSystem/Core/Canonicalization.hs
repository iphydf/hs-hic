{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

module Language.Hic.TypeSystem.Core.Canonicalization
    ( minimize
    , bisimilar
    , minimizeGraph
    , normalizeGraph
    ) where

import           Language.Hic.Core.TypeSystem           (TypeInfo)
import           Language.Hic.TypeSystem.Core.TypeGraph (fromTypeInfo,
                                                         minimizeGraph,
                                                         normalizeGraph,
                                                         toTypeInfo)

-- | Minimizes an equi-recursive type by merging bisimilar nodes and returning
-- a canonical tree representation.
--
-- This is the core algorithm for ensuring that recursive types don't unroll
-- indefinitely during solving.
minimize :: TypeInfo p -> TypeInfo p
minimize t =
    let graph = fromTypeInfo t
        minGraph = minimizeGraph graph
        normGraph = normalizeGraph minGraph
    in toTypeInfo normGraph

-- | Checks if two equi-recursive types represent the same infinite tree.
bisimilar :: TypeInfo p -> TypeInfo p -> Bool
bisimilar t1 t2 = minimize t1 == minimize t2

