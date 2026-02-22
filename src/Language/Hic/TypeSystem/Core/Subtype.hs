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
import           Language.Hic.Core.TypeSystem                  (Phase (Local),
                                                                TemplateId)
import           Language.Hic.TypeSystem.Core.Base             (StdType (..),
                                                                isInt)
import           Language.Hic.TypeSystem.Core.Qualification    (Constness (..),
                                                                Nullability (..),
                                                                Ownership (..),
                                                                QualState (..),
                                                                allowCovariance,
                                                                stepQual)
import           Language.Hic.TypeSystem.Core.Transition.Types (RigidNodeF (..),
                                                                SpecialNode (..),
                                                                ValueStructure (..))
import           Language.Hic.TypeSystem.Core.TypeGraph        (TypeGraph,
                                                                tgNodes, tgRoot)

-- | Evaluates if `gActual` is a valid subtype of `gExpected` under strict C
-- rules (e.g. enforcing pointer invariance where required).
subtypeOfGraph :: forall p. (Ord (TemplateId p)) => TypeGraph p -> TypeGraph p -> Bool
subtypeOfGraph gActual gExpected =
    evalState (check QualTop (tgRoot gActual) (tgRoot gExpected)) Set.empty
  where
    getNode node_id graph
        | node_id == -1 = RSpecial SUnconstrained
        | node_id == -2 = RSpecial SConflict
        | otherwise = IntMap.findWithDefault (RSpecial SConflict) node_id (tgNodes graph)

    check :: QualState -> Int -> Int -> State (Set.Set (Int, Int)) Bool
    check q iAct iExp = do
        seen <- get
        if Set.member (iAct, iExp) seen then return True
        else do
            modify (Set.insert (iAct, iExp))
            let nAct = getNode iAct gActual
                nExp = getNode iExp gExpected
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
                        let isConstExp = cExp == QConst'
                            qNext = stepQual q isConstExp

                        case (vAct, vExp) of
                            (VBuiltin bAct, VBuiltin bExp) -> do
                                let valOk = bAct == bExp || (isInt bAct && isInt bExp && bAct <= bExp)
                                return $ if cov then valOk else bAct == bExp

                            (VSingleton bAct vAct', VSingleton bExp vExp') -> return $ bAct == bExp && vAct' == vExp'
                            (VSingleton bAct _, VBuiltin bExp) -> do
                                let valOk = bAct == bExp || (isInt bAct && isInt bExp && bAct <= bExp)
                                return $ if cov then valOk else False

                            (VPointer tAct' nAct' oAct', VPointer tExp' nExp' oExp') -> do
                                let nOk = if cov then nAct' <= nExp' else nAct' == nExp'
                                let oOk = if cov then oAct' <= oExp' else oAct' == oExp'
                                if not nOk || not oOk then return False
                                else check qNext tAct' tExp'

                            (VArray mAct' dsAct', VArray mExp' dsExp') -> do
                                let sizeOk = null dsExp' || length dsAct' == length dsExp'
                                if not sizeOk then return False
                                else do
                                    let tAct' = fromMaybe (-1) mAct'
                                        tExp' = fromMaybe (-1) mExp'
                                    check qNext tAct' tExp'

                            (VArray mAct' dsAct', VPointer tExp' nExp' oExp') -> do
                                let tAct' = fromMaybe (-1) mAct'
                                let nOk = if cov then QUnspecified <= nExp' else QUnspecified == nExp'
                                let oOk = if cov then QNonOwned' <= oExp' else QNonOwned' == oExp'
                                if not nOk || not oOk then return False
                                else check qNext tAct' tExp'

                            (VPointer _ _ _, VArray _ _) -> return False

                            -- nullptr_t subtyping
                            (VBuiltin NullPtrTy, VPointer _ nExp' _) -> return $ nExp' /= QNonnull'
                            (VSingleton NullPtrTy _, VPointer _ nExp' _) -> return $ nExp' /= QNonnull'

                            -- Other structural matches
                            (VTemplate ftAct _ _, VTemplate ftExp _ _) -> return $ ftAct == ftExp
                            (VTypeRef rAct _ asAct, VTypeRef rExp _ asExp) -> return $ rAct == rExp && asAct == asExp
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
                        retOk <- check QualTop rAct rExp
                        paramsOk <- zipWithM (\a b -> check QualTop b a) pAct pExp -- Contravariant!
                        return (retOk && and paramsOk)

                _ -> return False
