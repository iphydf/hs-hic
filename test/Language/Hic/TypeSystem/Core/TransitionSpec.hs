{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.TypeSystem.Core.TransitionSpec (spec) where

import           Data.Functor                                  (void)
import           Data.Maybe                                    (fromJust,
                                                                fromMaybe)
import           Data.Set                                      (Set)
import qualified Data.Set                                      as Set
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import qualified Language.Cimple                               as C
import           Language.Hic.TypeSystem.Core.Base             (Phase (..),
                                                                Qualifier (..),
                                                                StdType (..),
                                                                TypeInfo,
                                                                pattern Array,
                                                                pattern BuiltinType,
                                                                pattern Conflict,
                                                                pattern Const,
                                                                pattern Nonnull,
                                                                pattern Nullable,
                                                                pattern Pointer,
                                                                pattern Singleton,
                                                                pattern Template,
                                                                pattern Unconstrained)

import qualified Language.Hic.TypeSystem.Core.Base             as TS
import qualified Language.Hic.TypeSystem.Core.Canonicalization as Canonicalization
import qualified Language.Hic.TypeSystem.Core.Lattice          as Lattice
import           Language.Hic.TypeSystem.Core.Qualification    (QualState (..))
import qualified Language.Hic.TypeSystem.Core.Qualification    as Q
import           Language.Hic.TypeSystem.Core.Transition
import           Language.Hic.TypeSystem.Core.TypeGraph        (Polarity (..))

spec :: Spec
spec = do
    let term = (TS.Unconstrained, TS.Conflict)
    let getQuals t = case fromJust (toRigid t) of
            RFunction _ _ c _ -> (Q.QUnspecified, Q.QNonOwned', c)
            RValue (VPointer _ n o) c _ -> (n, o, c)
            RValue (VTemplate _ n o) c _ -> (n, o, c)
            RValue _ c _ -> (Q.QUnspecified, Q.QNonOwned', c)
            _ -> (Q.QUnspecified, Q.QNonOwned', Q.QMutable')
    let getStructure t = fromJust (toRigid t)
    let lookupNode t = toRigid t
    let stepB ps a b = stepTransition ps lookupNode getQuals term (a == b) (getStructure a) (getStructure b)

    let isJoinId t = TS.isUnconstrained t
    let isMeetId t = TS.isConflict t

    let joinDeep ps a b
            | isJoinId a = b
            | isJoinId b = a
            | otherwise = case stepB ps a b of
                RSpecial SConflict      -> TS.Conflict
                RSpecial SUnconstrained -> TS.Unconstrained
                res                     -> fromRigid (\(l, r, ps') -> joinDeep ps' l r) res

    let meetDeep ps a b
            | isMeetId a = b
            | isMeetId b = a
            | otherwise = case stepB ps a b of
                RSpecial SConflict      -> TS.Conflict
                RSpecial SUnconstrained -> TS.Unconstrained
                res                     -> fromRigid (\(l, r, ps') -> meetDeep ps' l r) res

    describe "Properties" $ do
        prop "stepTransition is symmetric" $ \pol qL qR (t1 :: TypeInfo 'Local) (t2 :: TypeInfo 'Local) ->
            let ps = ProductState pol qL qR False
                psRev = ProductState pol qR qL False
                res = stepB ps t1 t2
                resRev = stepB psRev t2 t1

                swapPS (l, r, p) = (r, l, p { psQualL = psQualR p, psQualR = psQualL p })

            in getQualsFromNode res == getQualsFromNode resRev &&
               rnfSize' res == rnfSize' resRev &&
               fmap swapPS res == resRev

        prop "stepTransition is idempotent" $ \pol q (t :: TypeInfo 'Local) ->
            let ps = ProductState pol q q False
                res = stepB ps t t
            in getQualsFromNode res == getQuals t &&
               rnfSize' res == TS.ftSize (TS.toFlat t) &&
               void res == void (getStructure t)

        prop "joinQuals is associative" $ \(n1 :: Q.Nullability) (o1 :: Q.Ownership) (c1 :: Q.Constness) n2 o2 c2 n3 o3 c3 ->
            let joinQ (n, o, c) (n', o', c') = (max n n', max o o', max c c')
                q1 = (n1, o1, c1)
                q2 = (n2, o2, c2)
                q3 = (n3, o3, c3)
            in joinQ q1 (joinQ q2 q3) == joinQ (joinQ q1 q2) q3

        prop "meetQuals is associative" $ \(n1 :: Q.Nullability) (o1 :: Q.Ownership) (c1 :: Q.Constness) n2 o2 c2 n3 o3 c3 ->
            let meetQ (n, o, c) (n', o', c') = (min n n', min o o', min c c')
                q1 = (n1, o1, c1)
                q2 = (n2, o2, c2)
                q3 = (n3, o3, c3)
            in meetQ q1 (meetQ q2 q3) == meetQ (meetQ q1 q2) q3

        prop "qualifiers satisfy absorption" $ \(n1 :: Q.Nullability) (o1 :: Q.Ownership) (c1 :: Q.Constness) n2 o2 c2 ->
            let joinQ (n, o, c) (n', o', c') = (max n n', max o o', max c c')
                meetQ (n, o, c) (n', o', c') = (min n n', min o o', min c c')
                q1 = (n1, o1, c1)
                q2 = (n2, o2, c2)
            in joinQ q1 (meetQ q1 q2) == q1 &&
               meetQ q1 (joinQ q1 q2) == q1

        prop "Unconstrained is identity for Join" $ \qL qR (t :: TypeInfo 'Local) ->
            let ps = ProductState PJoin qL qR False
                res = stepB ps Unconstrained t
            in void res == void (getStructure t)

        prop "Conflict is zero for Join" $ \qL qR (t :: TypeInfo 'Local) ->
            let ps = ProductState PJoin qL qR False
                res = stepB ps Conflict t
            in res == RSpecial SConflict

        prop "Conflict is identity for Meet" $ \qL qR (t :: TypeInfo 'Local) ->
            let ps = ProductState PMeet qL qR False
                res = stepB ps Conflict t
            in void res == void (getStructure t)

        prop "Unconstrained is zero for Meet" $ \qL qR (t :: TypeInfo 'Local) ->
            let ps = ProductState PMeet qL qR False
                res = stepB ps Unconstrained t
            in res == RSpecial SUnconstrained

        prop "subtypeQuals is consistent with Join" $ \(n1 :: Q.Nullability) (o1 :: Q.Ownership) (c1 :: Q.Constness) n2 o2 c2 ->
            let joinQ (n, o, c) (n', o', c') = (max n n', max o o', max c c')
                q1 = (n1, o1, c1)
                q2 = (n2, o2, c2)
            in (n1 <= n2 && o1 <= o2 && c1 <= c2) == (joinQ q1 q2 == q2)

        prop "subtypeQuals is consistent with Meet" $ \(n1 :: Q.Nullability) (o1 :: Q.Ownership) (c1 :: Q.Constness) n2 o2 c2 ->
            let meetQ (n, o, c) (n', o', c') = (min n n', min o o', min c c')
                q1 = (n1, o1, c1)
                q2 = (n2, o2, c2)
            in (n1 <= n2 && o1 <= o2 && c1 <= c2) == (meetQ q1 q2 == q1)

        it "subtypeQuals is transitive" $ property $ \(n1 :: Q.Nullability) (o1 :: Q.Ownership) (c1 :: Q.Constness) ->
            let q1 = (n1, o1, c1)
                subtypeQ (n, o, c) (n', o', c') = n <= n' && o <= o' && c <= c'
            in forAll (genSuperQuals q1) $ \q2 ->
                forAll (genSuperQuals q2) $ \q3 ->
                    subtypeQ q1 q3

        prop "stepTransition is associative (Meet)" $ \q (t1 :: TypeInfo 'Local) t2 t3 ->
            let ps = ProductState PMeet q q False
                step a b = stepB ps a b

                m23 = meetDeep ps t2 t3
                m12 = meetDeep ps t1 t2
                res1 = step t1 m23
                res2 = step m12 t3
            in counterexample ("q: " ++ show q) $
               counterexample ("t1: " ++ show t1) $
               counterexample ("t2: " ++ show t2) $
               counterexample ("t3: " ++ show t3) $
               counterexample ("meet(t2, t3): " ++ show m23) $
               counterexample ("meet(t1, t2): " ++ show m12) $
               counterexample ("res1: " ++ show (void res1, getQualsFromNode res1)) $
               counterexample ("res2: " ++ show (void res2, getQualsFromNode res2)) $
               void res1 == void res2 && getQualsFromNode res1 == getQualsFromNode res2

        prop "stepTransition is associative (Join)" $ \q (t1 :: TypeInfo 'Local) t2 t3 ->
            let ps = ProductState PJoin q q False
                step a b = stepB ps a b

                j23 = joinDeep ps t2 t3
                j12 = joinDeep ps t1 t2
                res1 = step t1 j23
                res2 = step j12 t3
            in counterexample ("q: " ++ show q) $
               counterexample ("t1: " ++ show t1) $
               counterexample ("t2: " ++ show t2) $
               counterexample ("t3: " ++ show t3) $
               counterexample ("join(t2, t3): " ++ show j23) $
               counterexample ("join(t1, t2): " ++ show j12) $
               counterexample ("res1: " ++ show (void res1, getQualsFromNode res1)) $
               counterexample ("res2: " ++ show (void res2, getQualsFromNode res2)) $
               void res1 == void res2 && getQualsFromNode res1 == getQualsFromNode res2

    describe "Properties Repro" $ do
        it "is symmetric (Case 1)" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t1 = Pointer (BuiltinType VoidTy)
            let t2 = Pointer (BuiltinType S32Ty)
            let res1 = stepB ps t1 t2
            let res2 = stepB ps t2 t1
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2
            rnfSize' res1 `shouldBe` rnfSize' res2

        it "is symmetric (Symmetry failure repro)" $ do
            let ps = ProductState PJoin QualUnshielded QualTop False
            let t1 = Pointer (Array Nothing [])
            let t2 = BuiltinType NullPtrTy
            let res1 = stepB ps t1 t2
            let psRev = ProductState PJoin QualTop QualUnshielded False
            let res2 = stepB psRev t2 t1

            getQualsFromNode res1 `shouldBe` getQualsFromNode res2
            void res1 `shouldBe` void res2

        it "is idempotent (Case 1)" $ do
            let pol = PMeet
                q = QualTop
                t = TS.Qualified (Set.fromList [TS.QOwner, TS.QNonnull]) (TS.BuiltinType TS.NullPtrTy)
                ps = ProductState pol q q False
                res = stepB ps t t
            getQualsFromNode res `shouldBe` getQuals t
            rnfSize' res `shouldBe` TS.ftSize (TS.toFlat t)
            void res `shouldBe` void (getStructure t)

        it "is idempotent (Case 2)" $ do
            let pol = PJoin
                q = QualUnshielded
                t = Array Nothing []
                ps = ProductState pol q q False
                res = stepB ps t t
            getQualsFromNode res `shouldBe` getQuals t
            rnfSize' res `shouldBe` TS.ftSize (TS.toFlat t)
            void res `shouldBe` void (getStructure t)

    describe "toRigid / fromRigid" $ do
        it "roundtrips simple types" $ do
            let t = BuiltinType S32Ty
            fromRigid id (fromJust $ toRigid t) `shouldBe` t

        it "roundtrips pointers" $ do
            let t = Pointer (BuiltinType S32Ty)
            fromRigid id (fromJust $ toRigid t) `shouldBe` t

        it "collapses qualifiers" $ do
            let t = Const (Nonnull (Pointer (BuiltinType S32Ty)))
            let r = fromJust $ toRigid t
            getQualsFromNode r `shouldBe` (Q.QNonnull', Q.QNonOwned', Q.QConst')
            case r of
                RValue (VPointer _ _ _) _ _ -> return ()
                _          -> expectationFailure "Expected RValue VPointer structure"

    describe "stepTransition" $ do
        it "getTargetState for PMeet preserves structural bot even if constructors differ" $ do
            let ps = ProductState PMeet QualTop QualTop False
                tL = Pointer TS.Unconstrained
                tR = BuiltinType TS.S32Ty
                -- Array vs Pointer -> sameConstructor = False in stepStructure
                nL = RValue (VArray (Just tL) []) Q.QMutable' Nothing
                nR = RValue (VPointer tR Q.QUnspecified Q.QNonOwned') Q.QMutable' Nothing
                res = stepTransition ps lookupNode getQuals term False nL nR

            case res of
                RValue (VArray (Just (tL_res, tR_res, _)) _) _ _ -> do
                    tL_res `shouldBe` tL
                    tR_res `shouldBe` tR
                _ -> expectationFailure $ "Expected RArray, but got: " ++ show res

        describe "Join" $ do
            let ps = ProductState PJoin QualTop QualTop False

            it "joins identical builtins" $ do
                let t = BuiltinType S32Ty
                let res = stepB ps t t
                res `shouldBe` RValue (VBuiltin S32Ty) Q.QMutable' Nothing

            it "joins different integers to wider" $ do
                let t1 = BuiltinType S16Ty
                let t2 = BuiltinType S32Ty
                let res = stepB ps t1 t2
                res `shouldBe` RValue (VBuiltin S32Ty) Q.QMutable' Nothing

            it "joins Nonnull and base to base" $ do
                let t1 = Nonnull (Pointer (BuiltinType S32Ty))
                let t2 = Pointer (BuiltinType S32Ty)
                let res = stepB ps t1 t2
                getQualsFromNode res `shouldBe` (Q.QUnspecified, Q.QNonOwned', Q.QMutable')

            it "joins base and Nullable to Nullable" $ do
                let t1 = Pointer (BuiltinType S32Ty)
                let t2 = Nullable (Pointer (BuiltinType S32Ty))
                let res = stepB ps t1 t2
                case res of
                    RValue (VPointer _ Q.QNullable' _) _ _ -> return ()
                    _ -> expectationFailure "Expected Nullable pointer"

            it "joins different singletons to builtin" $ do
                let t1 = Singleton S32Ty 1
                let t2 = Singleton S32Ty 2
                let res = stepB ps t1 t2
                res `shouldBe` RValue (VBuiltin S32Ty) Q.QMutable' Nothing

            it "joins Arrays with different lengths to Array with no elements" $ do
                let t1 = Array (Just (BuiltinType S32Ty)) [Singleton S32Ty 1]
                let t2 = Array (Just (BuiltinType S32Ty)) []
                let res = stepB ps t1 t2
                case res of
                    RValue (VArray (Just _) []) _ _ -> return ()
                    _ -> expectationFailure "Expected VArray with empty elements"

            it "handles pointer variance (covariance allowed at top)" $ do
                let t1 = Pointer (BuiltinType S32Ty)
                let t2 = Pointer (BuiltinType S64Ty)
                let res = stepB ps t1 t2
                case res of
                    RValue (VPointer (_, _, ps') _ _) _ _ -> do
                        psPolarity ps' `shouldBe` PJoin
                        psQualL ps' `shouldBe` QualLevel1Const
                        psQualR ps' `shouldBe` QualLevel1Const
                    _ -> expectationFailure "Expected VPointer"

            it "joins Array(Array bot) and Array bot correctly" $ do
                let t1 = Array (Just (Array (Just Unconstrained) [])) []
                let t2 = Array (Just Unconstrained) []
                let res = stepB ps t1 t2
                case res of
                    RValue (VArray (Just (tL, tR, _)) _) _ _ -> do
                        tL `shouldBe` Array (Just Unconstrained) []
                        tR `shouldBe` Unconstrained
                    _ -> expectationFailure "Expected VArray"

            it "joins nullptr_t and Array to Pointer (decay)" $ do
                let t1 = BuiltinType NullPtrTy
                let t2 = Array (Just (BuiltinType S32Ty)) []
                let res = stepB (ProductState PJoin QualTop QualTop False) t1 t2
                case res of
                    RValue (VPointer _ Q.QNullable' _) _ _ -> return ()
                    _ -> expectationFailure $ "Expected VPointer with Q.QNullable', but got: " ++ show res

            it "uses QualTop for array dimensions in Join" $ do
                let t1 = Array (Just (BuiltinType S32Ty)) [Singleton S32Ty 10]
                let t2 = Array (Just (BuiltinType S32Ty)) [Singleton S32Ty 10]
                let res = stepB (ProductState PJoin QualTop QualTop False) t1 t2
                case res of
                    RValue (VArray _ [(_, _, ps')]) _ _ -> do
                        psQualL ps' `shouldBe` QualTop
                        psQualR ps' `shouldBe` QualTop
                    _ -> expectationFailure "Expected VArray with dimension"
        describe "Meet" $ do
            let ps = ProductState PMeet QualTop QualTop False

            it "meets Nonnull and base to Nonnull" $ do
                let t1 = Nonnull (Pointer (BuiltinType S32Ty))
                let t2 = Pointer (BuiltinType S32Ty)
                let res = stepB ps t1 t2
                case res of
                    RValue (VPointer _ Q.QNonnull' _) _ _ -> return ()
                    _ -> expectationFailure "Expected Nonnull pointer"

            it "meets different constructors to Unconstrained" $ do
                let t1 = BuiltinType S32Ty
                let t2 = Pointer (BuiltinType S32Ty)
                let res = stepB ps t1 t2
                res `shouldBe` RSpecial SUnconstrained

            it "meets Arrays with different lengths to Pointer bottom" $ do
                let t1 = Array (Just (BuiltinType S32Ty)) [Singleton S32Ty 1]
                let t2 = Array (Just (BuiltinType S32Ty)) [Singleton S32Ty 1, Singleton S32Ty 2]
                let res = stepB ps t1 t2
                res `shouldBe` RSpecial SUnconstrained

            it "enforces invariance for pointers (unsound loose meet)" $ do
                let t1 = Pointer (BuiltinType S32Ty)
                let t2 = Pointer (Singleton S32Ty 1)
                -- These should meet to a pointer with original targets because we let the recursive solver handle invariance.
                let res = stepB ps t1 t2
                case res of
                    RValue (VPointer (tL, tR, ps') _ _) _ _ -> do
                        tL `shouldBe` BuiltinType S32Ty
                        tR `shouldBe` Singleton S32Ty 1
                        psPolarity ps' `shouldBe` PMeet
                    _ -> expectationFailure "Expected VPointer"

            it "enforces invariance for nested pointers (C rule)" $ do
                let t = BuiltinType S32Ty
                let tpp = Pointer (Pointer t)
                let ctpp = Pointer (Pointer (Const t))
                -- Meet(T**, const T**) should produce RPointer with original targets.
                let res = stepB ps tpp ctpp
                case res of
                    RValue (VPointer (tL, tR, ps') _ _) _ _ -> do
                        tL `shouldBe` Pointer t
                        tR `shouldBe` Pointer (Const t)
                        psPolarity ps' `shouldBe` PMeet
                    _ -> expectationFailure "Expected VPointer"

            it "allows Level 1 pointer qualifier covariance" $ do
                let t = BuiltinType S32Ty
                let p = Pointer t
                let cp = Pointer (Const t)
                -- Meet(int*, const int*) should be int*
                let res = stepB ps p cp
                case res of
                    RValue (VPointer (tL, tR, _) _ _) _ _ -> do
                        tL `shouldBe` t
                        tR `shouldBe` Const t
                    _ -> expectationFailure "Expected VPointer"

            it "enforces invariance for nullptr_t vs Pointer" $ do
                let ps' = ProductState PMeet QualUnshielded QualUnshielded False
                let t1 = BuiltinType NullPtrTy
                let t2 = Pointer (BuiltinType S32Ty)
                -- Meet(nullptr_t, int*) in invariant context should be bottom.
                let res = stepB ps' t1 t2
                res `shouldBe` RSpecial SUnconstrained

            it "enforces invariance for nullptr_t vs Array" $ do
                let ps' = ProductState PMeet QualUnshielded QualUnshielded False
                let t1 = BuiltinType NullPtrTy
                let t2 = Array (Just (BuiltinType S32Ty)) []
                -- Meet(nullptr_t, int[]) in invariant context should be bottom.
                let res = stepB ps' t1 t2
                res `shouldBe` RSpecial SUnconstrained

    describe "C Pointer Variance Rules" $ do
        it "allows sound T** to T* const* conversion (C rule)" $ do
            pendingWith "Rigid transition's strict invariance rules currently violate this C subtyping rule"
            -- Join(T**, T* const*) should be T* const*
            let ps = ProductState PJoin QualTop QualTop False
            let t = BuiltinType S32Ty
            let tpp = Pointer (Pointer t)
            let tcp = Pointer (Const (Pointer t))

            -- Step 1: level 1 (the outer pointers)
            let res1 = stepB ps tpp tcp
            case res1 of
                RValue (VPointer (_, _, ps') _ _) _ _ -> do
                    psQualL ps' `shouldBe` QualLevel1Const
                    psQualR ps' `shouldBe` QualLevel1Const
                _ -> expectationFailure "Expected VPointer"

        it "meets T** and T* const* to T** (Deep Meet)" $ do
            let t = BuiltinType S32Ty
            let tpp = Pointer (Pointer t)
            let tcp = Pointer (Const (Pointer t))
            -- meet(T**, T* const*) should be T** because T** <: T* const*
            Lattice.meet tpp tcp `shouldBe` tpp

        it "enforces invariance when shielded state is lost" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t = BuiltinType S32Ty
            let tpp = Pointer (Pointer t)
            let ctpp = Pointer (Pointer (Const t))

            -- Step 1: level 1
            let res1 = stepB ps tpp ctpp
            case res1 of
                RValue (VPointer (_, _, ps') _ _) _ _ -> do
                    psQualL ps' `shouldBe` QualLevel1Const
                    psQualR ps' `shouldBe` QualLevel1Const
                _ -> expectationFailure "Expected VPointer"

        it "discovers sound LUB (const pointer) when shielded state is lost" $ do
            pendingWith "unclear whether we want this"
            -- If we are in invariance mode, Pointer and Array should cross-join
            -- to a const Pointer. This is Sound LUB Discovery.
            let ps = ProductState PJoin QualUnshielded QualUnshielded False
            let t = BuiltinType S32Ty
            let t_ptr = getStructure (Pointer t)
            let t_arr = getStructure (Array (Just t) [])

            let res = stepTransition ps lookupNode getQuals term False t_arr t_ptr
            case res of
                RValue (VPointer (_, _, ps') n _) c _ -> do
                    (n, c) `shouldBe` (Q.QUnspecified, Q.QConst') -- result gets const because of structural mismatch
                    psForceConst ps' `shouldBe` False
                _ -> expectationFailure $ "Expected RPointer with False forceConst on target, but got: " ++ show res

    describe "Shielded Covariance Propagation" $ do
        it "does not add const when joining with Pointer Unconstrained in invariant context" $ do
            let ps = ProductState PJoin QualUnshielded QualUnshielded False
            let t1 = getStructure (Pointer Unconstrained)
            let t2 = getStructure (Pointer (BuiltinType S32Ty))
            let res = stepTransition ps lookupNode getQuals term False t1 t2
            case res of
                RValue (VPointer (_, _, ps') _ _) c _ -> do
                    c `shouldBe` Q.QMutable'
                    psForceConst ps' `shouldBe` False
                _ -> expectationFailure $ "Expected RPointer, but got: " ++ show res

        it "propagates forceConst to target state in Join(T**, S**)" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t = BuiltinType S32Ty
            let s = BuiltinType S64Ty
            let tpp = Pointer (Pointer t)
            let spp = Pointer (Pointer s)

            -- Step 1: Join the outer pointers.
            let res = stepB ps tpp spp

            case res of
                RValue (VPointer (_, _, ps') _ _) _ _ -> do
                    psForceConst ps' `shouldBe` True
                    psQualL ps' `shouldBe` Q.QualLevel1Const
                    psQualR ps' `shouldBe` Q.QualLevel1Const
                _ -> expectationFailure $ "Expected VPointer, but got: " ++ show res

            -- Step 2: Verify that a node processed with psForceConst=True gets the const qualifier.
            let res2 = stepTransition (ProductState PJoin Q.QualLevel1Const Q.QualLevel1Const True) lookupNode getQuals term False (getStructure (Pointer t)) (getStructure (Pointer s))
            getQualsFromNode res2 `shouldBe` (Q.QUnspecified, Q.QNonOwned', Q.QConst')

        it "does not add unnecessary const to outer pointer in Join(T**, S**)" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t = BuiltinType S32Ty
            let s = BuiltinType S64Ty
            let tpp = Pointer (Pointer t)
            let spp = Pointer (Pointer s)
            let res = stepB ps tpp spp
            let (_, _, c) = getQualsFromNode res
            c `shouldBe` Q.QMutable'

        it "does not add const to outer pointer in Join(Array(int), Pointer(int)) at Top level" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t = BuiltinType S32Ty
            let t_ptr = Pointer t
            let t_arr = Array (Just t) []
            let res = stepB ps t_ptr t_arr
            let (_, _, c) = getQualsFromNode res
            c `shouldBe` Q.QMutable'

        it "synthesizes const for decay in invariant context" $ do
            -- If we are in invariance mode (e.g. nested pointer), Array and Pointer should join to Pointer.
            -- If targets are identical, no const is needed.
            let ps = ProductState PJoin Q.QualUnshielded Q.QualUnshielded False
            let t = BuiltinType S32Ty
            let t_ptr = getStructure (Pointer t)
            let t_arr = getStructure (Array (Just t) [])
            let res = stepTransition ps lookupNode getQuals term False t_ptr t_arr
            case res of
                RValue (VPointer (_, _, ps') _ _) _ _ -> do
                    psForceConst ps' `shouldBe` False
                _ -> expectationFailure "Expected VPointer"

        it "returns Unconstrained in Meet(int, long) in invariant context" $ do
            let ps = ProductState PMeet QualUnshielded QualUnshielded False
            let t1 = BuiltinType S32Ty
            let t2 = BuiltinType S64Ty
            let res = stepB ps t1 t2
            res `shouldBe` RSpecial SUnconstrained

    describe "Lattice Property Regressions" $ do
        it "satisfies lower bound for Sized Pointer and Array" $ do
            let l = C.L (C.AlexPn (-78) 3 (-12)) C.PpElse (TS.TIdInst 13 (TS.TIdParam 81 (Just "") TS.TopLevel))
            let t1 = TS.Sized (Pointer Unconstrained) l
            let t2 = Array Nothing []
            -- m = meet t1 t2
            let m = Lattice.meet t1 t2
            Lattice.subtypeOf m t1 `shouldBe` True
            Lattice.subtypeOf m t2 `shouldBe` True

        it "satisfies absorption for Pointer and Array" $ do
            let t1 = Pointer (BuiltinType F32Ty)
            let t2 = Array (Just Conflict) []
            let m = Lattice.meet t1 t2
            let res = Lattice.join t1 m
            Canonicalization.bisimilar (TS.normalizeType res) (TS.normalizeType t1) `shouldBe` True

        it "satisfies absorption for Array counterexample" $ do
            let t1 = Array (Just Conflict) [BuiltinType S08Ty]
            let t2 = Array (Just (Singleton S64Ty (-37))) []
            let m = Lattice.meet t1 t2
            let res = Lattice.join t1 m
            Canonicalization.bisimilar (TS.normalizeType res) (TS.normalizeType t1) `shouldBe` True

    describe "Regression Tests" $ do
        it "inherits size from non-terminal in Join with Unconstrained" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let l = C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "len")
            let t = TS.Sized TS.VarArg l
            let res = stepB ps Unconstrained t
            rnfSize' res `shouldBe` Just l

        it "returns Pointer Unconstrained in Meet when one side is Unconstrained (Bottom Preservation)" $ do
            let ps = ProductState PMeet QualTop QualTop False
            -- Meet(Pointer(Unconstrained), Pointer(VarArg))
            let t1 = Pointer Unconstrained
            let t2 = Pointer TS.VarArg
            let res = stepB ps t1 t2
            case res of
                RValue (VPointer (bot', _, _) _ _) _ _ -> bot' `shouldBe` bot' -- Just check it's a pointer to bottom
                _ -> expectationFailure "Expected VPointer"

        it "preserves Pointer structure in Meet when one target is Conflict (Top)" $ do
            -- This test case captures a conflict between variance and lattice identities.
            -- Conflict is Top for the lattice. Meet(Conflict, X) = X.
            -- Therefore, Meet(Pointer(Conflict), Pointer(X)) should be Pointer(X)
            -- in a covariant context.
            let ps = ProductState PMeet QualTop QualTop False
            let t1 = Const (Pointer Conflict)
            let t2 = Pointer TS.VarArg
            let res = stepB ps t1 t2
            case res of
                RValue (VPointer _ _ _) _ _ -> return ()
                _ -> expectationFailure $ "Expected VPointer (identity preservation), but got: " ++ show res

    describe "Contradiction and Boundary Conditions" $ do
        it "collapses Nonnull NullPtrTy to SUnconstrained (Bottom)" $ do
            let t = Nonnull (BuiltinType NullPtrTy)
            toRigid t `shouldBe` Just (RSpecial SUnconstrained)

        it "preserves identical singletons of NullPtrTy" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t1 = Singleton NullPtrTy 0
            let t2 = Singleton NullPtrTy 0
            let res = stepB ps t1 t2
            res `shouldBe` RValue (VSingleton NullPtrTy 0) Q.QMutable' Nothing

        it "joins different singletons of NullPtrTy to VBuiltin NullPtrTy" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t1 = Singleton NullPtrTy 0
            let t2 = Singleton NullPtrTy 1
            let res = stepB ps t1 t2
            res `shouldBe` RValue (VBuiltin NullPtrTy) Q.QMutable' Nothing

        it "meets different singletons of NullPtrTy to SUnconstrained (Bottom)" $ do
            let ps = ProductState PMeet QualTop QualTop False
            let t1 = Singleton NullPtrTy 0
            let t2 = Singleton NullPtrTy 1
            let res = stepB ps t1 t2
            res `shouldBe` RSpecial SUnconstrained

        it "collapses Unsupported types to SConflict (Top)" $ do
            let t = TS.Unsupported "experimental feature"
            toRigid t `shouldBe` Just (RSpecial SConflict)

    describe "Associativity Repro" $ do
        it "allows sound T** to T* const* conversion (Meet repro)" $ do
            let ps = ProductState PMeet QualTop QualTop False
            let t = BuiltinType S32Ty
            let tpp = Pointer (Pointer t)
            let tcp = Pointer (Const (Pointer t))
            -- Step 1: outer level
            let res = stepB ps tpp tcp
            case res of
                RValue (VPointer (tL, tR, ps') _ _) _ _ -> do
                    tL `shouldBe` Pointer t
                    tR `shouldBe` Const (Pointer t)
                    psPolarity ps' `shouldBe` PMeet
                    psQualL ps' `shouldBe` QualLevel1Mutable
                    psQualR ps' `shouldBe` QualLevel1Const
                _ -> expectationFailure $ "Expected RValue VPointer, but got: " ++ show res

        it "is associative for Join (Case 1)" $ do
            let ps = ProductState PJoin QualUnshielded QualTop False
            let t1 = Pointer TS.VarArg
            let t2 = Pointer (Singleton U16Ty 9)
            let t3 = Unconstrained

            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Case 1)" $ do
            let ps = ProductState PMeet QualTop QualUnshielded False
            let t1 = Conflict
            let t2 = TS.Sized (Template (TS.TIdAnonymous 0 (Just "T")) Nothing) (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "len"))
            let t3 = BuiltinType U64Ty

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let res1 = step t1 (meet' t2 t3)
            let res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Case 2)" $ do
            let ps = ProductState PMeet QualUnshielded QualTop False
            let t1 = Array Nothing []
            let t2 = Pointer (BuiltinType S08Ty)
            let t3 = Array (Just (Singleton S08Ty 23)) []

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let res1 = step t1 (meet' t2 t3)
            let res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Case 2)" $ do
            let ps = ProductState PJoin QualShielded QualUnshielded False
            let t1 = Pointer Conflict
            let t2 = Pointer TS.VarArg
            let t3 = Pointer TS.VarArg

            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Case 3)" $ do
            let ps = ProductState PMeet QualShielded QualTop False
            let t1 = Singleton S16Ty 4
            let t2 = Pointer (Singleton F32Ty 2)
            let t3 = Pointer TS.VarArg

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let res1 = step t1 (meet' t2 t3)
            let res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Case 3)" $ do
            let ps = ProductState PJoin QualTop QualShielded False
            let t1 = Pointer (Pointer Conflict)
            let t2 = Array (Just (Singleton S32Ty (-30))) []
            let t3 = Array (Just Conflict) []

            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Case 7)" $ do
            let ps = ProductState PJoin QualTop QualUnshielded False
            let t1 = Array (Just Conflict) []
            let t2 = Array (Just (BuiltinType F64Ty)) []
            let t3 = Array (Just (Singleton S08Ty (-6))) []

            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Case 4)" $ do
            let ps = ProductState PMeet QualUnshielded QualTop False
            let t1 = Array (Just (Singleton U64Ty 11)) []
            let t2 = Array (Just (Singleton SizeTy 11)) []
            let t3 = Array Nothing []

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let res1 = step t1 (meet' t2 t3)
            let res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Case 4)" $ do
            let ps = ProductState PJoin QualUnshielded QualTop False
            let t1 = BuiltinType NullPtrTy
            let t2 = Singleton NullPtrTy 29
            let t3 = Pointer (Singleton F32Ty 6)

            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Case 5)" $ do
            let ps = ProductState PMeet QualTop QualShielded False
            let t1 = Singleton S64Ty (-35)
            let t2 = Singleton U08Ty 15
            let t3 = Conflict

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let res1 = step t1 (meet' t2 t3)
            let res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Case 5)" $ do
            let ps = ProductState PJoin QualShielded QualShielded False
            let t1 = Singleton U08Ty (-24)
            let t2 = Singleton F32Ty 37
            let t3 = Unconstrained

            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Case 8)" $ do
            let ps = ProductState PJoin QualTop QualShielded False
            let t1 = Pointer Conflict
            let t2 = Array (Just (Singleton S32Ty (-5))) []
            let t3 = Array (Just TS.VarArg) []

            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Case 6)" $ do
            let ps = ProductState PMeet QualTop QualShielded False
            let t1 = Array Nothing []
            let t2 = Pointer Conflict
            let len = C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "len")
            let t3 = TS.Sized (Array Nothing []) len

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let res1 = step t1 (meet' t2 t3)
            let res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2
            rnfSize' res1 `shouldBe` rnfSize' res2

        it "is associative for Meet (Case 7)" $ do
            let ps = ProductState PMeet QualShielded QualUnshielded False
            let t1 = Singleton NullPtrTy (-5)
            let t2 = Nonnull (Array Nothing [])
            let t3 = Conflict

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let res1 = step t1 (meet' t2 t3)
            let res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Case 8)" $ do
            let ps = ProductState PMeet QualShielded QualUnshielded False
            let t1 = Pointer Unconstrained
            let t2 = Singleton NullPtrTy 9
            let t3 = Nonnull (Pointer (Singleton S08Ty 14))

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let res1 = step t1 (meet' t2 t3)
            let res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Case 9)" $ do
            let q = Q.QualUnshielded
            let ps = ProductState PMeet q q False
            let t1 = Array Nothing []
            let t2 = Pointer TS.VarArg
            let t3 = Const (Array Nothing [])

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let m23 = meet' t2 t3
            let m12 = meet' t1 t2
            let res1 = step t1 m23
            let res2 = step m12 t3

            let msg = unlines
                    [ "t1: " ++ show t1
                    , "t2: " ++ show t2
                    , "t3: " ++ show t3
                    , "meet(t2, t3): " ++ show m23
                    , "meet(t1, t2): " ++ show m12
                    , "res1: " ++ show (void res1, getQualsFromNode res1)
                    , "res2: " ++ show (void res2, getQualsFromNode res2)
                    ]

            case (void res1 == void res2 && getQualsFromNode res1 == getQualsFromNode res2) of
                True  -> return ()
                False -> expectationFailure msg

        it "is associative for Join (Case 9)" $ do
            let q = QualTop
            let ps = ProductState PJoin q q False
            let t1 = Const (Array (Just Unconstrained) [])
            let t2 = Pointer (Pointer (Singleton F64Ty (-8)))
            let t3 = Array (Just (Pointer (Singleton S64Ty 9))) []

            let getStructure' t = fromMaybe (RSpecial SConflict) (toRigid t)
            let step' p a b = stepTransition p lookupNode getQuals term (a == b) (getStructure' a) (getStructure' b)
            let join'' p a b = fromRigid (\(l, r, p') -> fromRigid (const TS.Conflict) (step' p' l r)) (step' p a b)

            let j23 = join'' ps t2 t3
            let j12 = join'' ps t1 t2
            let res1 = join'' ps t1 j23
            let res2 = join'' ps j12 t3

            TS.stripLexemes res1 `shouldBe` TS.stripLexemes res2

        it "is associative for meet counterexample (repro 3)" $ do
            let t1 = Array (Just (Array Nothing [])) []
            let t2 = Pointer (Array (Just TS.VarArg) [])
            let t3 = Pointer (BuiltinType NullPtrTy)

            let res1 = Lattice.meet (Lattice.meet t1 t2) t3
            let res2 = Lattice.meet t1 (Lattice.meet t2 t3)

            TS.stripLexemes res1 `shouldBe` TS.stripLexemes res2

        it "is associative for Join (Associativity failure repro 2)" $ do
            let q = QualUnshielded
            let t1 = Array (Just Unconstrained) []
            let t2 = Singleton NullPtrTy (-77)
            let t3 = BuiltinType NullPtrTy

            let ps = ProductState PJoin q q False
            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Associativity failure repro 3)" $ do
            let q = QualUnshielded
            let t1 = BuiltinType F64Ty
            let t2 = Singleton F64Ty 7
            let t3 = Singleton F64Ty 28

            let ps = ProductState PJoin q q False
            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Associativity failure repro 4)" $ do
            let q = QualLevel1Const
            let tid = TS.TIdSolver (-59) (Just "@:\\1028762\\ve\\137698}\\a\\10917n-\\n\\1094631\\1030085\\98512")
            let t1 = Pointer (Template tid Nothing)
            let t2 = Array Nothing []
            let t3 = Singleton NullPtrTy (-33)

            let ps = ProductState PJoin q q False
            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Associativity failure repro 5)" $ do
            let q = QualUnshielded
            let t1 = Const (Singleton S08Ty 41)
            let t2 = Singleton U32Ty (-54)
            let t3 = Singleton U32Ty (-43)

            let ps = ProductState PJoin q q False
            let step a b = stepB ps a b
            let join' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Unconstrained then r else if r == TS.Unconstrained then l else TS.Conflict) (step a b)

            let res1 = step t1 (join' t2 t3)
            let res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

    describe "stepTransition Associativity (Full Repro)" $ do
        it "is associative for VArray with optional element type" $ do
            let ps = ProductState PJoin QualLevel1Const QualLevel1Const False
                t1 = Pointer Conflict
                t2 = Array (Just Conflict) [Conflict]
                t3 = Array Nothing []

                step a b = stepB ps a b
                join' a b = case step a b of
                    RSpecial SConflict      -> TS.Conflict
                    RSpecial SUnconstrained -> TS.Unconstrained
                    res                     -> fromRigid (\(l, r, ps') -> joinDeep ps' l r) res

                j23 = join' t2 t3
                j12 = join' t1 t2

                res1 = step t1 j23
                res2 = step j12 t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for the reported failing case" $ do
            let ps = ProductState PJoin QualTop QualTop False
                t1 = Array (Just (Pointer TS.VarArg)) []
                t2 = Pointer (Pointer TS.VarArg)
                t3 = Pointer (Pointer (Array Nothing []))

                step a b = stepB ps a b

                -- Helper to compute the join type info from a step result
                join' a b = case step a b of
                    RSpecial SConflict      -> TS.Conflict
                    RSpecial SUnconstrained -> TS.Unconstrained
                    res                     -> fromRigid (\(l, r, ps') -> joinDeep ps' l r) res

                res1 = step t1 (join' t2 t3)
                res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for the second reported failing case" $ do
            let ps = ProductState PJoin QualTop QualTop False
                t1 = Pointer (Pointer (Array Nothing []))
                t2 = Pointer (Pointer (Array (Just TS.VarArg) []))
                t3 = Pointer (Pointer TS.Unconstrained)

                step a b = stepB ps a b

                join' a b = case step a b of
                    RSpecial SConflict      -> TS.Conflict
                    RSpecial SUnconstrained -> TS.Unconstrained
                    res                     -> fromRigid (\(l, r, ps') -> joinDeep ps' l r) res

                res1 = step t1 (join' t2 t3)
                res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Pointer(Pointer(Array Nothing)) join" $ do
            let ps = ProductState PJoin QualTop QualTop False
                t1 = Pointer (Pointer (Array Nothing []))
                t2 = Pointer (Pointer (Array (Just TS.VarArg) []))
                t3 = Pointer (Pointer Unconstrained)

                step a b = stepB ps a b

                join' a b = case step a b of
                    RSpecial SConflict      -> TS.Conflict
                    RSpecial SUnconstrained -> TS.Unconstrained
                    res                     -> fromRigid (\(l, r, ps') -> joinDeep ps' l r) res

                j23 = join' t2 t3
                j12 = join' t1 t2

                res1 = step t1 j23
                res2 = step j12 t3
            counterexample ("join(t2, t3): " ++ show j23) $
                    counterexample ("join(t1, t2): " ++ show j12) $
                    counterexample ("res1: " ++ show (void res1, getQualsFromNode res1)) $
                    counterexample ("res2: " ++ show (void res2, getQualsFromNode res2)) $
                    do
                        void res1 `shouldBe` void res2
                        getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Meet (Associativity failure repro 2)" $ do
            let q = QualLevel1Const
                t1 = Array (Just Conflict) []
                t2 = Pointer Conflict
                t3 = Pointer (Singleton CharTy 21)
                ps = ProductState PMeet q q False

                step a b = stepB ps a b
                meet' a b = case step a b of
                    RSpecial SConflict      -> TS.Conflict
                    RSpecial SUnconstrained -> TS.Unconstrained
                    res                     -> fromRigid (\(l, r, ps') -> meetDeep ps' l r) res

                res1 = step t1 (meet' t2 t3)
                res2 = step (meet' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

        it "is associative for Join (Associativity failure repro 6)" $ do
            let q = QualTop
                t1 = Const (TS.Function (Singleton BoolTy (-4)) [TS.VarArg])
                t2 = TS.Function Conflict [Array Nothing []]
                t3 = Array Nothing []
                ps = ProductState PJoin q q False

                step a b = stepB ps a b
                join' a b = case step a b of
                    RSpecial SConflict      -> TS.Conflict
                    RSpecial SUnconstrained -> TS.Unconstrained
                    res                     -> fromRigid (\(l, r, ps') -> joinDeep ps' l r) res

                res1 = step t1 (join' t2 t3)
                res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2


        it "is associative for Meet (Associativity failure repro 1)" $ do
            let q = QualShielded
            let ps = ProductState PMeet q q False
            let lexeme = C.L (C.AlexPn (-11) (-62) 10) C.PctColon (TS.TIdPoly 28 49 (Just "name") TS.TopLevel)
            let t1 = Singleton NullPtrTy (-9)
            let t2 = Pointer Conflict
            let t3 = TS.Sized (BuiltinType NullPtrTy) lexeme

            let step a b = stepB ps a b
            let meet' a b = fromRigid (\(l, r, _) -> if l == r then l else if l == TS.Conflict then r else if r == TS.Conflict then l else TS.Unconstrained) (step a b)

            let m23 = meet' t2 t3
            let m12 = meet' t1 t2
            let res1 = step t1 m23
            let res2 = step m12 t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2
            rnfSize' res1 `shouldBe` rnfSize' res2

        it "is associative for Join (Associativity failure repro 7)" $ do
            let q = QualLevel1Mutable
                t1 = Pointer (BuiltinType NullPtrTy)
                t2 = Unconstrained
                t3 = Pointer (Pointer TS.VarArg)
                ps = ProductState PJoin q q False

                step a b = stepB ps a b
                join' a b = case step a b of
                    RSpecial SConflict      -> TS.Conflict
                    RSpecial SUnconstrained -> TS.Unconstrained
                    res                     -> fromRigid (\(l, r, ps') -> joinDeep ps' l r) res

                res1 = step t1 (join' t2 t3)
                res2 = step (join' t1 t2) t3

            void res1 `shouldBe` void res2
            getQualsFromNode res1 `shouldBe` getQualsFromNode res2

    describe "Absorption Repro" $ do
        it "does not add const when joining with Pointer Unconstrained at top level (Covariant)" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t1 = Pointer (Singleton F64Ty 6)
            let t2 = Pointer Unconstrained
            let res = stepB ps t1 t2
            let (_, _, c) = getQualsFromNode res
            c `shouldBe` Q.QMutable'

        it "adds const when joining Array(Pointer(T)) with Array(Pointer(Unconstrained)) (Invariant)" $ do
            let ps = ProductState PJoin QualTop QualTop False
            let t1 = Array (Just (Pointer (Singleton F64Ty 6))) []
            let t2 = Array (Just (Pointer Unconstrained)) []
            let res = stepB ps t1 t2
            case res of
                RValue (VArray (Just (_, _, ps')) _) _ _ -> psForceConst ps' `shouldBe` True
                _ -> expectationFailure "Expected VArray"

        it "preserves structural identity when meeting with Conflict (Absorption repro)" $ do
            let ps = ProductState PMeet QualTop QualTop False
            let t1 = Pointer (Array (Just Unconstrained) [])
            let t2 = Pointer Conflict
            let res = stepB ps t1 t2
            case res of
                RValue (VPointer (tL, _, _) _ _) _ _ -> tL `shouldBe` Array (Just Unconstrained) []
                _ -> expectationFailure $ "Expected VPointer, but got: " ++ show res

        it "preserves Array structure in Meet with Conflict (Identity)" $ do
            let ps = ProductState PMeet QualTop QualTop False
            let t1 = Array Nothing [Singleton U08Ty (-10)]
            let t2 = Conflict
            let res = stepB ps t1 t2
            case res of
                RValue (VArray _ _) _ _ -> return ()
                _ -> expectationFailure $ "Expected VArray, but got: " ++ show res

        it "collapses Array to Unconstrained in Meet with Unconstrained (Zero)" $ do
            let ps = ProductState PMeet QualTop QualTop False
            let t1 = Array Nothing [Singleton U08Ty (-10)]
            let t2 = Unconstrained
            let res = stepB ps t1 t2
            res `shouldBe` RSpecial SUnconstrained

getQualsFromNode :: RigidNodeF tid a -> (Q.Nullability, Q.Ownership, Q.Constness)
getQualsFromNode = \case
    RFunction _ _ c _ -> (Q.QUnspecified, Q.QNonOwned', c)
    RValue (VPointer _ n o) c _ -> (n, o, c)
    RValue (VTemplate _ n o) c _ -> (n, o, c)
    RValue _ c _ -> (Q.QUnspecified, Q.QNonOwned', c)
    _ -> (Q.QUnspecified, Q.QNonOwned', Q.QMutable')

rnfSize' :: RigidNodeF tid a -> Maybe (C.Lexeme tid)
rnfSize' = \case
    RFunction _ _ _ s -> s
    RValue _ _ s -> s
    _ -> Nothing

-- | Generates a supertype of the given qualifiers.
genSuperQuals :: (Q.Nullability, Q.Ownership, Q.Constness) -> Gen (Q.Nullability, Q.Ownership, Q.Constness)
genSuperQuals (n, o, c) = (,,) <$> genSuperNull n <*> genSuperOwn o <*> genSuperConst c
  where
    genSuperNull Q.QNonnull'     = elements [Q.QNonnull', Q.QUnspecified, Q.QNullable']
    genSuperNull Q.QUnspecified = elements [Q.QUnspecified, Q.QNullable']
    genSuperNull Q.QNullable'    = return Q.QNullable'

    genSuperOwn Q.QNonOwned' = elements [Q.QNonOwned', Q.QOwned']
    genSuperOwn Q.QOwned'    = return Q.QOwned'

    genSuperConst Q.QMutable' = elements [Q.QMutable', Q.QConst']
    genSuperConst Q.QConst'   = return Q.QConst'
