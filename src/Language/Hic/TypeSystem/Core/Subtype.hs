{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.TypeSystem.Core.Subtype
    ( subtypeOfGraph
    ) where

import           Control.Monad.State
import           Control.Monad                                 (zipWithM)
import qualified Data.IntMap.Strict                            as IntMap
import           Data.Maybe                                    (fromMaybe)
import qualified Data.Set                                      as Set
import           Language.Hic.Core.TypeSystem                  (FullTemplateF (..),
                                                                Phase (Local),
                                                                TemplateId)
import           Language.Hic.TypeSystem.Core.Base             (StdType (..),
                                                                isInt)
import           Language.Hic.TypeSystem.Core.Qualification    (Constness (..),
                                                                Nullability (..),
                                                                Ownership (..),
                                                                QualState (..),
                                                                allowCovariance)
import           Language.Hic.TypeSystem.Core.Transition.Types (RigidNodeF (..),
                                                                SpecialNode (..),
                                                                ValueStructure (..))
import           Language.Hic.TypeSystem.Core.TypeGraph        (TypeGraph,
                                                                tgNodes, tgRoot)

-- | Like 'stepQual' but once invariant, stay invariant.  In C, a mutable
-- intermediate pointer level makes ALL deeper levels invariant regardless
-- of their constness.  The transition's 'stepQual' allows rescue because
-- it tracks left/right states independently; in the single-state subtype
-- check we must be stricter.
stepSubtype :: QualState -> Bool -> QualState
stepSubtype QualTop True              = QualLevel1Const
stepSubtype QualTop False             = QualLevel1Mutable
stepSubtype QualLevel1Const _         = QualShielded
stepSubtype QualLevel1Mutable _       = QualUnshielded
stepSubtype QualShielded _            = QualShielded
stepSubtype QualUnshielded _          = QualUnshielded

-- | Evaluates if `gActual` is a valid subtype of `gExpected` under strict C
-- rules (e.g. enforcing pointer invariance where required).
subtypeOfGraph :: forall p. (Ord (TemplateId p)) => TypeGraph p -> TypeGraph p -> Bool
subtypeOfGraph gActual gExpected =
    evalState (check QualTop gActual gExpected False (tgRoot gActual) (tgRoot gExpected)) Set.empty
  where
    getNode node_id graph
        | node_id == -1 = RSpecial SUnconstrained
        | node_id == -2 = RSpecial SConflict
        | otherwise = IntMap.findWithDefault (RSpecial SConflict) node_id (tgNodes graph)

    -- | gA is the "actual" (sub) graph, gE is the "expected" (super) graph.
    -- iAct indexes into gA, iExp indexes into gE.
    -- The Bool tracks whether graphs are swapped relative to the original call,
    -- so that the co-inductive cycle check distinguishes forward from
    -- contravariant comparisons (which swap the graphs).
    check :: QualState -> TypeGraph p -> TypeGraph p -> Bool -> Int -> Int -> State (Set.Set (Int, Int, Bool)) Bool
    check q gA gE swapped iAct iExp = do
        seen <- get
        if Set.member (iAct, iExp, swapped) seen then return True
        else do
            modify (Set.insert (iAct, iExp, swapped))
            let nAct = getNode iAct gA
                nExp = getNode iExp gE
            case (nAct, nExp) of
                (RSpecial SConflict, RSpecial SConflict) -> return True
                (RSpecial SUnconstrained, RSpecial SUnconstrained) -> return True
                (_, RSpecial SConflict) -> return True  -- Anything <: Top
                (RSpecial SConflict, _) -> return False -- Top </: Anything else
                (RSpecial SUnconstrained, _) -> return True  -- Bottom <: Anything
                (_, RSpecial SUnconstrained) -> return False -- Anything else </: Bottom

                (RValue vAct cAct sAct, RValue vExp cExp sExp) -> do
                    let cov = allowCovariance q
                    let cOk = if cov then cAct <= cExp else cAct == cExp
                    let sOk = sAct == sExp || sExp == Nothing

                    if not cOk || not sOk then return False
                    else do
                        -- Step the FSM based on the CHILD node's constness,
                        -- not the current node's.  In C, `const int *` stores
                        -- the const on the child (int) node while the pointer
                        -- node itself is mutable.  The const shield that
                        -- enables covariant widening comes from the child
                        -- being const, matching the transition's getTargetState.
                        let childConst nid g = case getNode nid g of
                                RValue _ c _ -> c
                                RFunction _ _ c _ -> c
                                _ -> QMutable'
                            qChild tExpChild = stepSubtype q (childConst tExpChild gE == QConst')

                        case (vAct, vExp) of
                            (VBuiltin bAct, VBuiltin bExp) -> do
                                let valOk = bAct == bExp || (isInt bAct && isInt bExp && bAct <= bExp)
                                return $ if cov then valOk else bAct == bExp

                            (VSingleton bAct vAct', VSingleton bExp vExp') ->
                                return $ vAct' == vExp' && (bAct == bExp || (cov && isInt bAct && isInt bExp && bAct <= bExp))
                            (VSingleton bAct _, VBuiltin bExp) -> do
                                let valOk = bAct == bExp || (isInt bAct && isInt bExp && bAct <= bExp)
                                -- A singleton is the same C type as its base builtin, so
                                -- Singleton b v <: Builtin b holds even at invariant positions.
                                -- Cross-type widening (e.g. S16Ty → S32Ty) still requires covariance.
                                return $ if cov then valOk else bAct == bExp

                            (VPointer tAct' nAct' oAct', VPointer tExp' nExp' oExp') -> do
                                let nOk = if cov then nAct' <= nExp' else nAct' == nExp'
                                let oOk = if cov then oAct' <= oExp' else oAct' == oExp'
                                if not nOk || not oOk then return False
                                else check (qChild tExp') gA gE swapped tAct' tExp'

                            (VArray mAct' dsAct', VArray mExp' dsExp') -> do
                                let sizeOk = null dsExp' || length dsAct' == length dsExp'
                                if not sizeOk then return False
                                else do
                                    let tAct' = fromMaybe (-1) mAct'
                                        tExp' = fromMaybe (-1) mExp'
                                    elemOk <- check (qChild tExp') gA gE swapped tAct' tExp'
                                    if not elemOk then return False
                                    else do
                                        -- Also check dimension compatibility
                                        dsOk <- zipWithM (\dA dE -> check QualTop gA gE swapped dA dE) dsAct' dsExp'
                                        return (and dsOk)

                            (VArray mAct' dsAct', VPointer tExp' nExp' oExp') -> do
                                let tAct' = fromMaybe (-1) mAct'
                                -- Arrays are inherently non-null in C, so at covariant
                                -- positions they satisfy any nullability constraint.
                                -- At invariant, use QUnspecified for consistency with
                                -- the transition's Pointer/Array merge result.
                                let nOk = if cov then True else QUnspecified == nExp'
                                let oOk = if cov then QNonOwned' <= oExp' else QNonOwned' == oExp'
                                if not nOk || not oOk then return False
                                else check (qChild tExp') gA gE swapped tAct' tExp'

                            (VPointer _ _ _, VArray _ _) -> return False

                            -- nullptr_t subtyping
                            (VBuiltin NullPtrTy, VPointer _ nExp' _) -> return $ nExp' /= QNonnull'
                            (VSingleton NullPtrTy _, VPointer _ nExp' _) -> return $ nExp' /= QNonnull'
                            (VBuiltin NullPtrTy, VArray _ _) -> return True
                            (VSingleton NullPtrTy _, VArray _ _) -> return True

                            -- Other structural matches
                            (VTemplate ftAct _ _, VTemplate ftExp _ _) -> return $ ftId ftAct == ftId ftExp
                            (VTypeRef rAct _ asAct, VTypeRef rExp _ asExp) ->
                                if rAct /= rExp || length asAct /= length asExp then return False
                                else do
                                    argsOk <- zipWithM (\a b -> check QualTop gA gE swapped a b) asAct asExp
                                    return (and argsOk)
                            (VExternal lAct, VExternal lExp) -> return $ lAct == lExp
                            (VVarArg, VVarArg) -> return True
                            (VNameLit lAct, VNameLit lExp) -> return $ lAct == lExp
                            (VEnumMem lAct, VEnumMem lExp) -> return $ lAct == lExp
                            (VIntLit lAct, VIntLit lExp) -> return $ lAct == lExp
                            _ -> return False

                (RFunction rAct pAct cAct sAct, RFunction rExp pExp cExp sExp) -> do
                    let cov = allowCovariance q
                    let cOk = if cov then cAct <= cExp else cAct == cExp
                    let sOk = sAct == sExp || sExp == Nothing
                    let pOk = length pAct == length pExp

                    if not cOk || not sOk || not pOk then return False
                    else do
                        retOk <- check QualTop gA gE swapped rAct rExp
                        -- Contravariant: swap graphs and indices for params
                        paramsOk <- zipWithM (\a b -> check QualTop gE gA (not swapped) b a) pAct pExp
                        return (retOk && and paramsOk)

                _ -> return False
