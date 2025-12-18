{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE StrictData #-}

module Language.Hic.Refined.SemanticEquality
    ( semEqStep
    , semEqResult
    ) where

import           Data.Bifunctor             (first)
import qualified Data.List                  as List
import           Data.Word                  (Word32)
import qualified Language.Cimple            as C
import           Language.Hic.Refined.State (ProductState (..))
import           Language.Hic.Refined.Types

-- | Checks if a 'StepResult' matches an original node (by applying a selector to 'ProductState').
-- Assumes both nodes are in canonical form (sorted collections).
semEqStep :: Eq tid => AnyRigidNodeF tid ProductState -> (ProductState -> Word32) -> AnyRigidNodeF tid Word32 -> Bool
semEqStep (AnyRigidNodeF n1) selector (AnyRigidNodeF n2) =
    case (n1, n2) of
        (RObject s1 q1, RObject s2 q2) -> q1 == q2 && semEqStepObj s1 selector s2
        (RReference r1 n1' o1 q1, RReference r2 n2' o2 q2) ->
            n1' == n2' && o1 == o2 && q1 == q2 && semEqStepRef r1 selector r2
        (RFunction a1 r1, RFunction a2 r2) ->
            length a1 == length a2 &&
            all (\(ps, expected) -> selector ps == expected) (zip a1 a2) &&
            semEqStepRet r1 selector r2
        (RTerminal t1, RTerminal t2) -> semEqTerminal t1 selector t2
        _ -> False

semEqTerminal :: TerminalNode ProductState -> (ProductState -> Word32) -> TerminalNode Word32 -> Bool
semEqTerminal SBottom _ SBottom = True
semEqTerminal SAny        _ SAny        = True
semEqTerminal SConflict   _ SConflict   = True
semEqTerminal (STerminal ps) selector (STerminal expected) = selector ps == expected
semEqTerminal _ _ _ = False

semEqStepObj :: Eq tid => ObjectStructure tid ProductState -> (ProductState -> Word32) -> ObjectStructure tid Word32 -> Bool
semEqStepObj s1 selector s2 = case (s1, s2) of
    (VBuiltin b1, VBuiltin b2) -> b1 == b2
    (VSingleton b1 v1, VSingleton b2 v2) -> b1 == b2 && v1 == v2
    (VNominal n1 p1, VNominal n2 p2) ->
        C.lexemeText n1 == C.lexemeText n2 && length p1 == length p2 && all (\(ps, expected) -> selector ps == expected) (zip p1 p2)
    (VEnum n1, VEnum n2) -> C.lexemeText n1 == C.lexemeText n2
    (VVar t1 i1, VVar t2 i2) -> t1 == t2 && i1 == i2
    (VExistential ts1 b1, VExistential ts2 b2) -> ts1 == ts2 && selector b1 == b2
    (VVariant m1, VVariant m2) ->
        fmap selector m1 == m2
    (VProperty a1 pk1, VProperty a2 pk2) -> pk1 == pk2 && selector a1 == a2
    (VSizeExpr m1, VSizeExpr m2) ->
        List.sortOn fst (map (first selector) m1) == List.sortOn fst m2
    _ -> False

semEqStepRef :: Eq tid => RefStructure tid ProductState -> (ProductState -> Word32) -> RefStructure tid Word32 -> Bool
semEqStepRef r1 selector r2 = case (r1, r2) of
    (Arr e1 d1, Arr e2 d2) ->
        selector e1 == e2 && length d1 == length d2 && all (\(ps, expected) -> selector ps == expected) (zip d1 d2)
    (Ptr p1, Ptr p2) -> semEqStepPtr p1 selector p2
    _ -> False

semEqStepPtr :: Eq tid => PtrTarget tid ProductState -> (ProductState -> Word32) -> PtrTarget tid Word32 -> Bool
semEqStepPtr p1 selector p2 = case (p1, p2) of
    (TargetObject o1, TargetObject o2) -> selector o1 == o2
    (TargetFunction a1 r1, TargetFunction a2 r2) ->
        length a1 == length a2 && all (\(ps, expected) -> selector ps == expected) (zip a1 a2) && semEqStepRet r1 selector r2
    (TargetOpaque t1, TargetOpaque t2) -> t1 == t2
    _ -> False

semEqStepRet :: ReturnType ProductState -> (ProductState -> Word32) -> ReturnType Word32 -> Bool
semEqStepRet r1 selector r2 = case (r1, r2) of
    (RetVal v1, RetVal v2) -> selector v1 == v2
    (RetVoid, RetVoid)     -> True
    _                      -> False

-- | Checks if two 'StepResult's are semantically equal (canonicalizing order/duplicates).
semEqResult :: Eq tid => AnyRigidNodeF tid ProductState -> AnyRigidNodeF tid ProductState -> Bool
semEqResult = (==) -- Results are guaranteed canonical by 'step'
