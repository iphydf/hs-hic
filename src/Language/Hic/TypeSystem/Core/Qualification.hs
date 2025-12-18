{-# LANGUAGE DeriveGeneric #-}
module Language.Hic.TypeSystem.Core.Qualification
    ( QualState (..)
    , Nullability (..)
    , Constness (..)
    , Ownership (..)
    , toQuals
    , fromQuals
    , stepQual
    , allowCovariance
    , joinQuals
    , meetQuals
    , subtypeQuals
    ) where

import           Data.Aeson                   (ToJSON)
import           Data.Set                     (Set)
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Language.Hic.Core.TypeSystem (Qualifier (..))
import           Test.QuickCheck              (Arbitrary (..),
                                               arbitraryBoundedEnum,
                                               genericShrink)

-- | State machine for C pointer qualification rules (C11 6.3.2.3).
-- Ensures structural termination by keeping the state space finite.
data QualState
    = QualTop          -- ^ Not inside a pointer.
    | QualLevel1Const  -- ^ At level 1, and it was 'const'.
    | QualLevel1Mutable -- ^ At level 1, and it was 'mutable'.
    | QualShielded     -- ^ All intermediate levels since depth 1 were 'const'.
    | QualUnshielded   -- ^ At least one intermediate level since depth 1 was NOT 'const'.
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance ToJSON QualState

instance Arbitrary QualState where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

-- | ADT for Hic Nullability Lattice: Nonnull < Unspecified < Nullable
data Nullability = QNonnull' | QUnspecified | QNullable'
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance Arbitrary Nullability where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

-- | ADT for C 'const' qualifier.
data Constness = QMutable' | QConst'
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance ToJSON Constness

instance Arbitrary Constness where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

-- | ADT for ownership (Hic extension).
data Ownership = QNonOwned' | QOwned'
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance ToJSON Ownership

instance Arbitrary Ownership where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

-- | Bridge from old representation.
toQuals :: Set Qualifier -> (Nullability, Ownership, Constness)
toQuals qs =
    let n = if Set.member QNullable qs then QNullable'
            else if Set.member QNonnull qs then QNonnull'
            else QUnspecified
        o = if Set.member QOwner qs then QOwned' else QNonOwned'
        c = if Set.member QConst qs then QConst' else QMutable'
    in (n, o, c)

-- | Bridge to old representation.
fromQuals :: Nullability -> Ownership -> Constness -> Set Qualifier
fromQuals n o c = Set.fromList $
    (case n of QNullable' -> [QNullable]; QNonnull' -> [QNonnull]; QUnspecified -> []) ++
    (case o of QOwned' -> [QOwner]; QNonOwned' -> []) ++
    (case c of QConst' -> [QConst]; QMutable' -> [])

-- | Transition function for the qualification FSM.
-- 'isConst' refers to whether the *target* (expected) level is qualified with 'const'.
stepQual :: QualState -> Bool -> QualState
stepQual QualTop isConst = if isConst then QualLevel1Const else QualLevel1Mutable
stepQual QualLevel1Const isConst = if isConst then QualShielded else QualUnshielded
stepQual QualLevel1Mutable isConst = if isConst then QualShielded else QualUnshielded
stepQual QualShielded isConst = if isConst then QualShielded else QualUnshielded
stepQual QualUnshielded _ = QualUnshielded

-- | Determines if covariance (actual <: expected) is allowed at the current level.
-- If not allowed, invariance (actual == expected) is required for soundness.
allowCovariance :: QualState -> Bool
allowCovariance QualTop           = True
allowCovariance QualLevel1Const   = True
allowCovariance QualLevel1Mutable = False
allowCovariance QualShielded      = True
allowCovariance QualUnshielded    = False

-- | Join two sets of qualifiers.
joinQuals :: Set Qualifier -> Set Qualifier -> Set Qualifier
joinQuals qs1 qs2 =
    let (n1, o1, c1) = toQuals qs1
        (n2, o2, c2) = toQuals qs2
    in fromQuals (max n1 n2) (max o1 o2) (max c1 c2)

-- | Meet two sets of qualifiers.
meetQuals :: Set Qualifier -> Set Qualifier -> Set Qualifier
meetQuals qs1 qs2 =
    let (n1, o1, c1) = toQuals qs1
        (n2, o2, c2) = toQuals qs2
    in fromQuals (min n1 n2) (min o1 o2) (min c1 c2)

-- | Check if one set of qualifiers is a subtype of another.
subtypeQuals :: Set Qualifier -> Set Qualifier -> Bool
subtypeQuals qs1 qs2 =
    let (n1, o1, c1) = toQuals qs1
        (n2, o2, c2) = toQuals qs2
    in n1 <= n2 && o1 <= o2 && c1 <= c2

