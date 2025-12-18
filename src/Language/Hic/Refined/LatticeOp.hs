{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData    #-}

module Language.Hic.Refined.LatticeOp
    ( Polarity (..)
    , Variance (..)
    , applyVariance
    , flipPol
    ) where

import           Data.Aeson   (ToJSON)
import           GHC.Generics (Generic)

-- | Polarity of the lattice operation.
-- PJoin: Least Upper Bound (Union / Generalization)
-- PMeet: Greatest Lower Bound (Intersection / Refinement)
data Polarity = PJoin | PMeet
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance ToJSON Polarity

-- | Variance of a constructor parameter.
data Variance = Covariant | Contravariant | Invariant
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

-- | Flips the polarity based on variance.
-- Used when traversing contravariant positions (function arguments).
applyVariance :: Variance -> Polarity -> Polarity
applyVariance Covariant p     = p
applyVariance Invariant _     = PMeet -- Invariance always forces refinement
applyVariance Contravariant p = flipPol p

flipPol :: Polarity -> Polarity
flipPol PJoin = PMeet
flipPol PMeet = PJoin
