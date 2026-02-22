{-# LANGUAGE RecordWildCards #-}
module Language.Hic.TypeSystem.Core.Transition.Variance
    ( getTargetState
    ) where

import           Language.Hic.TypeSystem.Core.Qualification    (Constness (..),
                                                                Nullability (..),
                                                                Ownership (..),
                                                                QualState (..),
                                                                allowCovariance,
                                                                stepQual)
import           Language.Hic.TypeSystem.Core.Transition.Types

-- | Computes the next state of the variance FSM for a pair of children.
-- Also determines if the merge is allowed (canJoin) and if a 'const' qualifier
-- must be forced (forceConst) to maintain soundness in an invariant context.
getTargetState :: (Eq a)
               => ProductState
               -> (a, a)      -- ^ (Bottom terminal, Top terminal)
               -> (a -> (Nullability, Ownership, Constness)) -- ^ Qualifier lookup
               -> Constness   -- ^ Qualifier of the current Left node
               -> Constness   -- ^ Qualifier of the current Right node
               -> a           -- ^ Left child node ID
               -> a           -- ^ Right child node ID
               -> (ProductState, Bool)
getTargetState ProductState{..} terminals getQuals _cL _cR tL tR =
    let (_, _, cChildL) = getQuals tL
        (_, _, cChildR) = getQuals tR

        nextL = stepQual psQualL (cChildL == QConst')
        nextR = stepQual psQualR (cChildR == QConst')

        isIdentity t = t == (if psPolarity == PJoin then fst terminals else snd terminals)
        isNeutral = isIdentity tL || isIdentity tR

        canJoin = isNeutral || psPolarity == PMeet || tL == tR || allowCovariance psQualL || allowCovariance psQualR
    in (ProductState psPolarity nextL nextR False, canJoin)
