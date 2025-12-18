{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Refined.Inference.LifterSpec (spec) where

import           Control.Monad.State.Strict            (runState)
import qualified Data.Map.Strict                       as Map
import           Data.Word                             (Word32)
import qualified Language.Cimple                       as C
import           Language.Hic.Refined.Inference.Lifter
import           Language.Hic.Refined.Inference.Types
import           Language.Hic.Refined.LatticeOp
import           Language.Hic.Refined.Registry
import           Language.Hic.Refined.Types
import qualified Language.Hic.TypeSystem.Core.Base     as TS
import           Test.Hspec

spec :: Spec
spec = do
    let emptyTS = Map.empty :: TS.TypeSystem
    let st0 = emptyTranslatorState emptyTS

    describe "liftImplicitPolymorphism" $ do
        it "identifies implicit parameters in structs" $ do
            -- struct Box { void *data; };
            -- void* data translates to a node containing a TIdParam PLocal ...
            -- Lifter should find this and promote it.
            let tidT = TIdParam PLocal 10 (Just "T")
            let varNode = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let member = Member (dummyL "data") 100
            let boxDef = StructDef (dummyL "Box") [] [member]
            let reg = Registry (Map.singleton "Box" boxDef)

            let st = st0 { tsNodes = Map.insert 100 varNode (tsNodes st0) }
            let (reg', st') = runState (liftImplicitPolymorphism reg) st

            let mDef = Map.lookup "Box" (regDefinitions reg')
            case mDef of
                Just (StructDef _ params _) -> params `shouldContain` [(tidT, Invariant)]
                _ -> expectationFailure "Expected Box to be a StructDef"

            -- Should also register an existential form
            Map.member "Box" (tsExistentials st') `shouldBe` True

        it "handles nested implicit polymorphism" $ do
            -- struct Inner { void *p; };
            -- struct Outer { struct Inner inner; };
            let tidT = TIdParam PLocal 10 (Just "T")
            let varNode = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let innerId = 100 :: Word32

            let memberP = Member (dummyL "p") innerId
            let innerDef = StructDef (dummyL "Inner") [] [memberP]

            let innerNominal = AnyRigidNodeF (RObject (VNominal (dummyL (TIdName "Inner")) [innerId]) (Quals False False))

            let memberI = Member (dummyL "inner") (102 :: Word32)
            let outerDef = StructDef (dummyL "Outer") [] [memberI]

            let reg = Registry (Map.fromList [("Inner", innerDef), ("Outer", outerDef)])
            let st = st0 { tsNodes = Map.fromList
                [ (innerId, varNode)
                , (102, innerNominal)
                ] }

            let (reg', _) = runState (liftImplicitPolymorphism reg) st

            case Map.lookup "Outer" (regDefinitions reg') of
                Just (StructDef _ params _) -> params `shouldContain` [(tidT, Invariant)]
                _ -> expectationFailure "Expected Outer to be a StructDef with lifted parameter T"

        it "preserves newly registered nodes during Pass 2" $ do
            -- struct Box { void *data; }; (implicitly polymorphic in T)
            -- Node 200: Box (with 0 params)
            -- liftImplicitPolymorphism should update Node 200 to Box<T>
            -- where T is a NEW node registered during the pass.
            let tidT = TIdParam PLocal 10 (Just "T")
            let varNode = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let member = Member (dummyL "data") 100
            let boxDef = StructDef (dummyL "Box") [(tidT, Invariant)] [member]
            let reg = Registry (Map.singleton "Box" boxDef)

            let nominalBox = AnyRigidNodeF (RObject (VNominal (dummyL (TIdName "Box")) []) (Quals False False))
            let st = st0 { tsNodes = Map.fromList [(100, varNode), (200, nominalBox)], tsNextId = 300 }

            let (_, st') = runState (liftImplicitPolymorphism reg) st

            -- Check if node 200 was updated
            case Map.lookup 200 (tsNodes st') of
                Just (AnyRigidNodeF (RObject (VNominal _ [paramId]) _)) -> do
                    -- The parameter node 'paramId' should exist in tsNodes!
                    Map.member paramId (tsNodes st') `shouldBe` True
                    case Map.lookup paramId (tsNodes st') of
                        Just (AnyRigidNodeF (RObject (VVar t _) _)) -> t `shouldBe` tidT
                        _ -> expectationFailure $ "Expected paramId " ++ show paramId ++ " to be a VVar node"
                _ -> expectationFailure "Expected node 200 to be updated to a VNominal with 1 parameter"

dummyL :: t -> C.Lexeme t
dummyL = C.L (C.AlexPn 0 0 0) C.IdSueType
