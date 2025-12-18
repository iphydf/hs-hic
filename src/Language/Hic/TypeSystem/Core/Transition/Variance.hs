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
getTargetState ProductState{..} terminals getQuals _ _ tL tR =
    let (_, _, cChildL) = getQuals tL
        (_, _, cChildR) = getQuals tR

        nextL_base = stepQual psQualL (cChildL == QConst')
        nextR_base = stepQual psQualR (cChildR == QConst')
        invariance_base = not (allowCovariance nextL_base || allowCovariance nextR_base)

        isIdentity t = t == (if psPolarity == PJoin then fst terminals else snd terminals)
        isNeutral = isIdentity tL || isIdentity tR

        -- Sound LUB discovery: force const only if targets differ and we are in an invariant context.
        -- Terminals (Unconstrained/Conflict) are neutral and don't trigger forceConst.
        forceConst = psPolarity == PJoin && not (tL == tR || isNeutral) && invariance_base

        nextL = if forceConst then stepQual psQualL True else nextL_base
        nextR = if forceConst then stepQual psQualR True else nextR_base

        canJoin = psPolarity == PMeet || tL == tR || isNeutral || allowCovariance nextL || allowCovariance nextR || forceConst
    in (ProductState psPolarity nextL nextR forceConst, canJoin)
