{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData    #-}

module Language.Hic.Refined.Lattice
    ( SubtypeResult (..)
    , NormalizationState (..)
    ) where

import           Data.Set                   (Set)
import           GHC.Generics               (Generic)
import           Language.Hic.Refined.State (ProductState)

-- | The result of a subtyping check (A <: B).
-- Conditional results allow for deferred template constraint solving.
data SubtypeResult
    = IsSubtype
    | NotSubtype
    | ConditionalSubtype (Set ProductState) -- ^ Subtype if these pairs are also subtypes
    deriving (Show, Eq, Ord, Generic)

-- | State used during the 'packNode' (normalization) pass.
-- Ensures logically impossible types collapse to SBottom.
data NormalizationState = NormalizationState
    { nsIsContradiction :: Bool
    , nsReason          :: Maybe String
    }
    deriving (Show, Eq, Ord, Generic)
