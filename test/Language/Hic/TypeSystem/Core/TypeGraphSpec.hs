{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.TypeSystem.Core.TypeGraphSpec (spec) where

import           Test.Hspec
import           Test.QuickCheck                               (property,
                                                                within)

import           Control.Monad                                 (unless)
import           Data.Maybe                                    (fromMaybe)


import qualified Language.Cimple                               as C
import           Language.Hic.TypeSystem.Core.Base             (Phase (..),
                                                                StdType (..),
                                                                TemplateId (..),
                                                                pattern Array,
                                                                pattern BuiltinType,
                                                                pattern Conflict,
                                                                pattern Const,
                                                                pattern Function,
                                                                pattern Pointer,
                                                                pattern Singleton,
                                                                pattern Sized,
                                                                pattern Template,
                                                                pattern Unconstrained,
                                                                pattern VarArg,
                                                                stripLexemes)
import qualified Language.Hic.TypeSystem.Core.Base             as TS
import qualified Language.Hic.TypeSystem.Core.Canonicalization as Canonicalization
import qualified Language.Hic.TypeSystem.Core.Lattice          as Lattice
import           Language.Hic.TypeSystem.Core.TypeGraph

spec :: Spec
spec = do
    let intTy = BuiltinType S32Ty
    let pInt = Pointer intTy

    it "round-trips a simple concrete type" $ do
        toTypeInfo (fromTypeInfo intTy) `shouldBe` intTy
        toTypeInfo (fromTypeInfo pInt) `shouldBe` pInt

    it "round-trips a recursive type" $ do
        -- T = Pointer T
        let t = Template (TIdRec 0) Nothing
        let recursive = Pointer t
        toTypeInfo (fromTypeInfo recursive) `shouldBe` recursive

    it "minimizes semantically equivalent graphs" $ do
        -- G1: 0 -> Pointer 0
        -- G2: 0 -> Pointer 1, 1 -> Pointer 0
        let g1 = fromTypeInfo (Pointer (Template (TIdRec 0) Nothing))
        let g2 = fromTypeInfo (Pointer (Pointer (Template (TIdRec 0) Nothing)))

        Canonicalization.minimizeGraph g1 `shouldBe` Canonicalization.minimizeGraph g2

    it "performs a recursive join correctly" $ within 1000000 $ do
        -- join(T = Pointer T, S = Pointer int) = R = Pointer (join(T, int)) = Pointer Conflict
        let t = Template (TIdRec 0) Nothing
        let g1 = fromTypeInfo (Pointer t)
        let g2 = fromTypeInfo (Pointer (BuiltinType S32Ty))

        let res = Lattice.joinGraph (const False) g1 g2
        toTypeInfo res `shouldBe` Pointer TS.Conflict

    it "joins Unconstrained and Sized VarArg correctly" $ do
        let l = C.L (C.AlexPn 0 0 0) C.IdVar (TIdName "len")
        let t1 = Unconstrained
        let t2 = Sized VarArg l
        let g1 = fromTypeInfo t1
        let g2 = fromTypeInfo t2
        let res = Lattice.joinGraph (const False) g1 g2
        -- join(Unconstrained, T) should be T.
        toTypeInfo res `shouldBe` t2

    it "meets Pointer Unconstrained and Pointer VarArg correctly" $ do
        let t1 = Pointer Unconstrained
        let t2 = Pointer VarArg
        let g1 = fromTypeInfo t1
        let g2 = fromTypeInfo t2
        let res = Lattice.meetGraph (const False) g1 g2
        -- Unconstrained is bottom.
        toTypeInfo res `shouldBe` Pointer Unconstrained

    it "is associative for complex Pointer Meet (repro)" $ do
        let a = Pointer (BuiltinType F64Ty)
        let b = Pointer (Singleton SizeTy (-1))
        let c = Pointer Unconstrained

        let gA = fromTypeInfo a
        let gB = fromTypeInfo b
        let gC = fromTypeInfo c

        let mBC = Lattice.meetGraph (const False) gB gC
        let m1 = Lattice.meetGraph (const False) gA mBC

        let mAB = Lattice.meetGraph (const False) gA gB
        let m2 = Lattice.meetGraph (const False) mAB gC

        stripLexemes (toTypeInfo m1) `shouldBe` stripLexemes (toTypeInfo m2)

    it "is associative for complex Pointer Meet (repro 2)" $ do
        let t1 = Array Nothing [BuiltinType S32Ty]
        let t2 = Array (Just Conflict) [Singleton S16Ty (-22)]
        let t3 = Pointer VarArg

        let g1 = fromTypeInfo t1
        let g2 = fromTypeInfo t2
        let g3 = fromTypeInfo t3

        let m23 = Lattice.meetGraph (const False) g2 g3
        let res1 = Lattice.meetGraph (const False) g1 m23

        let m12 = Lattice.meetGraph (const False) g1 g2
        let res2 = Lattice.meetGraph (const False) m12 g3

        stripLexemes (toTypeInfo res1) `shouldBe` stripLexemes (toTypeInfo res2)

    it "is associative for complex Pointer/Array Join (repro)" $ do
        let t1 = Pointer (Template (TIdName "T") Nothing)
        let t2 = Array (Just VarArg) []
        let t3 = Array (Just (Const (Array (Just Unconstrained) []))) []

        let g1 = fromTypeInfo t1
        let g2 = fromTypeInfo t2
        let g3 = fromTypeInfo t3

        let j23 = Lattice.joinGraph (const False) g2 g3
        let res1 = Lattice.joinGraph (const False) g1 j23

        let j12 = Lattice.joinGraph (const False) g1 g2
        let res2 = Lattice.joinGraph (const False) j12 g3

        stripLexemes (toTypeInfo res1) `shouldBe` stripLexemes (toTypeInfo res2)

    it "is associative for meet counterexample (repro)" $ do
        let t1 = Array (Just Conflict) []
            t2 = Pointer (Pointer Unconstrained)
            t3 = Array (Just (Pointer (Template (TIdRec 36) Nothing))) []
            g1 = fromTypeInfo t1
            g2 = fromTypeInfo t2
            g3 = fromTypeInfo t3
            m12 = Lattice.meetGraph (const False) g1 g2
            res1 = Lattice.meetGraph (const False) m12 g3
            m23 = Lattice.meetGraph (const False) g2 g3
            res2 = Lattice.meetGraph (const False) g1 m23
        stripLexemes (toTypeInfo res1) `shouldBe` stripLexemes (toTypeInfo res2)

    it "is associative for meet counterexample (repro 2)" $ do
        let t1 = Pointer (Array (Just (Singleton S32Ty (-29))) [])
            t2 = Pointer (Pointer (BuiltinType S16Ty))
            t3 = Pointer (Array Nothing [])
            g1 = fromTypeInfo t1
            g2 = fromTypeInfo t2
            g3 = fromTypeInfo t3
            m12 = Lattice.meetGraph (const False) g1 g2
            res1 = Lattice.meetGraph (const False) m12 g3
            m23 = Lattice.meetGraph (const False) g2 g3
            res2 = Lattice.meetGraph (const False) g1 m23
        stripLexemes (toTypeInfo res1) `shouldBe` stripLexemes (toTypeInfo res2)

    it "is associative for meet counterexample (repro 3)" $ do
        let t1 = Array (Just (Array Nothing [])) []
            t2 = Pointer (Array (Just VarArg) [])
            t3 = Pointer (BuiltinType NullPtrTy)
            g1 = fromTypeInfo t1
            g2 = fromTypeInfo t2
            g3 = fromTypeInfo t3
            m12 = Lattice.meetGraph (const False) g1 g2
            res1 = Lattice.meetGraph (const False) m12 g3
            m23 = Lattice.meetGraph (const False) g2 g3
            res2 = Lattice.meetGraph (const False) g1 m23
        stripLexemes (toTypeInfo res1) `shouldBe` stripLexemes (toTypeInfo res2)

    it "is associative for meet counterexample (repro 4)" $ do
        let t1 = Array Nothing [VarArg]
            t2 = Array Nothing []
            t3 = Pointer (Singleton NullPtrTy (-6))
            g1 = fromTypeInfo t1
            g2 = fromTypeInfo t2
            g3 = fromTypeInfo t3
            m12 = Lattice.meetGraph (const False) g1 g2
            res1 = Lattice.meetGraph (const False) m12 g3
            m23 = Lattice.meetGraph (const False) g2 g3
            res2 = Lattice.meetGraph (const False) g1 m23

        let msg = unlines
                [ "t1: " ++ show t1
                , "t2: " ++ show t2
                , "t3: " ++ show t3
                , "meet(t1, t2): " ++ show (toTypeInfo m12)
                , "meet(t2, t3): " ++ show (toTypeInfo m23)
                , "res1: " ++ show (toTypeInfo res1)
                , "res2: " ++ show (toTypeInfo res2)
                ]

        case Canonicalization.bisimilar (toTypeInfo res1) (toTypeInfo res2) of
            True  -> return ()
            False -> expectationFailure msg

    it "is associative for join counterexample (repro)" $ do
        let t1 = Const (Array (Just Unconstrained) [])
            t2 = Pointer (Pointer (Singleton F64Ty (-8)))
            t3 = Array (Just (Pointer (Singleton S64Ty 9))) []

            g1 = fromTypeInfo t1
            g2 = fromTypeInfo t2
            g3 = fromTypeInfo t3

            j12 = Lattice.joinGraph (const False) g1 g2
            res1 = Lattice.joinGraph (const False) j12 g3

            j23 = Lattice.joinGraph (const False) g2 g3
            res2 = Lattice.joinGraph (const False) g1 j23

            ti1 = toTypeInfo res1
            ti2 = toTypeInfo res2

        case Canonicalization.bisimilar ti1 ti2 of
            True -> return ()
            False -> expectationFailure $ unlines
                [ "t1: " ++ show t1
                , "t2: " ++ show t2
                , "t3: " ++ show t3
                , "join(t1, t2): " ++ show (toTypeInfo j12)
                , "join(t2, t3): " ++ show (toTypeInfo j23)
                , "res1: " ++ show ti1
                , "res2: " ++ show ti2
                ]

    it "is transitive for Sized recursive Function (repro)" $ do
        let tid = TIdName "F"
        let t1 = Function TS.VarArg [Template tid Nothing]
        let loc = C.L (C.AlexPn 0 0 0) C.PctPipePipe tid
        let a = Sized t1 loc
        let b = t1
        let c = t1
        -- a <: b and b <: c, so a <: c
        Lattice.subtypeOf a b `shouldBe` True
        Lattice.subtypeOf b c `shouldBe` True
        Lattice.subtypeOf a c `shouldBe` True

    describe "lfp (Least Fixed Point)" $ do
        it "introduces a cycle for a simple self-reference X = Pointer X" $ do
            let v = TS.FullTemplate (TS.TIdSolver 0 Nothing) Nothing
            -- f(X) = Pointer X
            let fx = fromTypeInfo (Pointer (Template (TS.ftId v) (TS.ftIndex v)))
            let res = lfp v fx
            -- Result should be T = Pointer T
            toTypeInfo res `shouldBe` Pointer (Template (TIdRec 0) Nothing)

        it "handles nested self-reference X = Pointer (Pointer X)" $ do
            let v = TS.FullTemplate (TS.TIdSolver 0 Nothing) Nothing
            let fx = fromTypeInfo (Pointer (Pointer (Template (TS.ftId v) (TS.ftIndex v))))
            let res = lfp v fx
            toTypeInfo res `shouldBe` Pointer (Pointer (Template (TIdRec 1) Nothing))

        it "is a no-op if the template is not present" $ do
            let v = TS.FullTemplate (TS.TIdSolver 0 Nothing) Nothing
            let fx = fromTypeInfo (Pointer (BuiltinType S32Ty))
            let res = lfp v fx
            toTypeInfo res `shouldBe` Pointer (BuiltinType S32Ty)

    describe "join is associative (regression tests)" $ do
        it "is associative for a known counterexample" $ do
            pendingWith "Join associativity is violated for some complex Pointer/Qualified types"
            let t1 = Array (Just (Pointer VarArg)) []
                t2 = Pointer (Pointer VarArg)
                t3 = Pointer (Pointer (Array Nothing []))
                g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
                g3 = fromTypeInfo t3
                j1 = Lattice.joinGraph (const False) g1 (Lattice.joinGraph (const False) g2 g3)
                j2 = Lattice.joinGraph (const False) (Lattice.joinGraph (const False) g1 g2) g3
            let r1 = toTypeInfo j1
                r2 = toTypeInfo j2
            unless (Canonicalization.bisimilar r1 r2) $
                expectationFailure $ "Join is not associative:\n  j1 = " ++ show r1 ++ "\n  j2 = " ++ show r2

        it "is associative for another known counterexample" $ do
            let t1 = Pointer (Pointer (Array Nothing []))
                t2 = Pointer (Pointer (Array (Just VarArg) []))
                t3 = Pointer (Pointer Unconstrained)
                g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
                g3 = fromTypeInfo t3
                j1 = Lattice.joinGraph (const False) g1 (Lattice.joinGraph (const False) g2 g3)
                j2 = Lattice.joinGraph (const False) (Lattice.joinGraph (const False) g1 g2) g3
            let r1 = toTypeInfo j1
            let r2 = toTypeInfo j2
            Canonicalization.bisimilar r1 r2 `shouldBe` True

        it "is associative for Join failure repro 1" $ do
            pendingWith "Hypothesis: join is not associative for complex Pointer/Qualified types, likely due to how getTargetState handles forceConst and QualState transitions."
            let t1 = Pointer (BuiltinType NullPtrTy)
                t2 = Unconstrained
                t3 = Pointer (Pointer VarArg)
                g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
                g3 = fromTypeInfo t3
                j1 = Lattice.joinGraph (const False) g1 (Lattice.joinGraph (const False) g2 g3)
                j2 = Lattice.joinGraph (const False) (Lattice.joinGraph (const False) g1 g2) g3
            let r1 = toTypeInfo j1
            let r2 = toTypeInfo j2
            unless (Canonicalization.bisimilar r1 r2) $
                expectationFailure $ "r1: " ++ show r1 ++ "\nr2: " ++ show r2

        it "is associative for Join failure repro 2" $ do
            pendingWith "Hypothesis: join is not associative for complex Pointer/Qualified types, likely due to how getTargetState handles forceConst and QualState transitions."
            let t1 = TS.Nullable (TS.Pointer (TS.Const (TS.Pointer (TS.Singleton TS.SizeTy 1))))
                t2 = Array (Just (Pointer Unconstrained)) []
                t3 = BuiltinType NullPtrTy
                g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
                g3 = fromTypeInfo t3
                j1 = Lattice.joinGraph (const False) g1 (Lattice.joinGraph (const False) g2 g3)
                j2 = Lattice.joinGraph (const False) (Lattice.joinGraph (const False) g1 g2) g3
            let r1 = toTypeInfo j1
            let r2 = toTypeInfo j2
            unless (Canonicalization.bisimilar r1 r2) $
                expectationFailure $ "r1: " ++ show r1 ++ "\nr2: " ++ show r2

    describe "properties" $ do
        it "round-trips any TypeInfo" $ property $ \(t :: TS.TypeInfo 'Global) ->
            Canonicalization.bisimilar (toTypeInfo (fromTypeInfo t)) t

        it "join is idempotent" $ property $ \(t :: TS.TypeInfo 'Global) ->
            let g = fromTypeInfo t
            in Canonicalization.bisimilar (toTypeInfo (Lattice.joinGraph (const False) g g)) (toTypeInfo g)

        it "join is commutative" $ property $ \(t1 :: TS.TypeInfo 'Global) (t2 :: TS.TypeInfo 'Global) ->
            let g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
            in Canonicalization.bisimilar (toTypeInfo (Lattice.joinGraph (const False) g1 g2)) (toTypeInfo (Lattice.joinGraph (const False) g2 g1))

        it "join is associative" $ property $ \(t1 :: TS.TypeInfo 'Global) (t2 :: TS.TypeInfo 'Global) (t3 :: TS.TypeInfo 'Global) ->
            let g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
                g3 = fromTypeInfo t3
                j1 = Lattice.joinGraph (const False) g1 (Lattice.joinGraph (const False) g2 g3)
                j2 = Lattice.joinGraph (const False) (Lattice.joinGraph (const False) g1 g2) g3
            in Canonicalization.bisimilar (toTypeInfo j1) (toTypeInfo j2)

        it "meet is idempotent" $ property $ \(t :: TS.TypeInfo 'Global) ->
            let g = fromTypeInfo t
            in Canonicalization.bisimilar (toTypeInfo (Lattice.meetGraph (const False) g g)) (toTypeInfo g)

        it "meet is commutative" $ property $ \(t1 :: TS.TypeInfo 'Global) (t2 :: TS.TypeInfo 'Global) ->
            let g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
            in Canonicalization.bisimilar (toTypeInfo (Lattice.meetGraph (const False) g1 g2)) (toTypeInfo (Lattice.meetGraph (const False) g2 g1))

        it "meet is associative" $ property $ \(t1 :: TS.TypeInfo 'Global) (t2 :: TS.TypeInfo 'Global) (t3 :: TS.TypeInfo 'Global) ->
            let g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
                g3 = fromTypeInfo t3
                m1 = Lattice.meetGraph (const False) g1 (Lattice.meetGraph (const False) g2 g3)
                m2 = Lattice.meetGraph (const False) (Lattice.meetGraph (const False) g1 g2) g3
            in Canonicalization.bisimilar (toTypeInfo m1) (toTypeInfo m2)

        it "substitute is consistent with tree substitution for concrete types" $ property $ \(t_val :: TS.TypeInfo 'Local) ->
            -- Use a fixed target to avoid issues with t_in generating unrelated templates.
            let v = TS.FullTemplate (TS.TIdSolver 0 Nothing) Nothing
                t_var = Template (TS.ftId v) (TS.ftIndex v)
                target = Pointer t_var
                g_target = fromTypeInfo target
                g_val = fromTypeInfo t_val
                g_res = substitute v g_val g_target
                t_res = toTypeInfo g_res
            in Canonicalization.minimize t_res `shouldBe` Canonicalization.minimize (Pointer t_val)
