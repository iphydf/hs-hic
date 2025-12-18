{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
module Language.Hic.TypeSystem.Core.Transition.Atoms
    ( isIdentityFor
    , isZeroFor
    , mergeAtoms
    ) where

import           Language.Hic.Core.TypeSystem                  (StdType (..))
import qualified Language.Hic.TypeSystem.Core.Base             as TS (isInt)
import           Language.Hic.TypeSystem.Core.Qualification    (allowCovariance)
import           Language.Hic.TypeSystem.Core.Transition.Types

-- | Determines if a node is a neutral identity for the given polarity.
-- Join: Unconstrained is identity.
-- Meet: Conflict is identity.
isIdentityFor :: Polarity -> RigidNodeF tid a -> Bool
isIdentityFor PJoin = \case
    RSpecial SUnconstrained -> True
    _ -> False
isIdentityFor PMeet = \case
    RSpecial SConflict -> True
    _ -> False

-- | Determines if a node is an annihilating zero for the given polarity.
-- Join: Conflict is zero.
-- Meet: Unconstrained is zero.
isZeroFor :: Polarity -> RigidNodeF tid a -> Bool
isZeroFor PJoin = \case
    RSpecial SConflict -> True
    _ -> False
isZeroFor PMeet = \case
    RSpecial SUnconstrained -> True
    _ -> False

-- | Merges atomic/scalar structures (Builtins, Singletons).
-- Returns Nothing if they are structurally incompatible.
mergeAtoms :: ProductState
           -> ValueStructure tid a
           -> ValueStructure tid a
           -> Maybe (ValueStructure tid a, Bool, Bool)
mergeAtoms ps@ProductState{..} sL sR =
    case (sL, sR) of
        (VBuiltin b1, VBuiltin b2)
            | b1 == b2 -> Just (VBuiltin b1, True, True)
            | TS.isInt b1 && TS.isInt b2 ->
                let resB = mergeInt psPolarity b1 b2
                in Just (VBuiltin resB, resB == b1, resB == b2)
            | otherwise -> Nothing

        (VSingleton b1 v1, VBuiltin b2) -> mergeS ProductState{..} b1 v1 b2
        (VBuiltin b1, VSingleton b2 v2) ->
            let psRev = ps { psQualL = psQualR, psQualR = psQualL }
            in case mergeAtoms psRev (VSingleton b2 v2) (VBuiltin b1) of
                Just (res, mR, mL) -> Just (res, mL, mR)
                Nothing            -> Nothing

        (VSingleton b1 v1, VSingleton b2 v2)
            | b1 == b2 && v1 == v2 -> Just (VSingleton b1 v1, True, True)
            | otherwise ->
                if TS.isInt b1 && TS.isInt b2 then
                    case psPolarity of
                        PJoin ->
                            let m = mergeInt PJoin b1 b2
                            in if v1 == v2 then Just (VSingleton m v1, m == b1, m == b2)
                               else Just (VBuiltin m, False, False)
                        PMeet ->
                            if v1 == v2 then Just (VSingleton (mergeInt PMeet b1 b2) v1, True, True)
                            else Nothing
                else if psPolarity == PJoin && b1 == b2 then Just (VBuiltin b1, False, False)
                else Nothing

        _ -> Nothing

mergeS :: ProductState -> StdType -> Integer -> StdType -> Maybe (ValueStructure tid a, Bool, Bool)
mergeS ProductState{..} b1 v1 b2 =
    if b1 == b2 || (TS.isInt b1 && TS.isInt b2)
    then case psPolarity of
        PJoin -> let resB = mergeInt PJoin b1 b2 in Just (VBuiltin resB, False, resB == b2)
        PMeet -> let resB = mergeInt PMeet b1 b2 in Just (VSingleton resB v1, resB == b1, False)
    else Nothing

mergeInt :: Polarity -> StdType -> StdType -> StdType
mergeInt PJoin b1 b2 = if b1 > b2 then b1 else b2
mergeInt PMeet b1 b2 = if b1 < b2 then b1 else b2
