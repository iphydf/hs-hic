{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Refined.Inference.SubstitutionSpec (spec) where

import           Control.Monad.State.Strict                  (get, modify,
                                                              runState)
import qualified Data.Map.Strict                             as Map
import qualified Data.Set                                    as Set
import           Data.Word                                   (Word32)
import qualified Language.Cimple                             as C
import           Language.Hic.Refined.Inference.Substitution
import           Language.Hic.Refined.Inference.Types
import           Language.Hic.Refined.Types
import qualified Language.Hic.TypeSystem.Core.Base           as TS
import           Test.Hspec
import           Test.QuickCheck

spec :: Spec
spec = do
    let emptyTS = Map.empty :: TS.TypeSystem
    let st0 = emptyTranslatorState emptyTS

    describe "substitute" $ do
        it "is identity for built-in types" $ do
            let (res, _) = runState (substitute (const $ return Nothing) 1) st0
            res `shouldBe` 1

        it "replaces a variable with its mapped node" $ do
            let tidT = TIdParam PLocal 10 (Just "T")
            let varNode = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let st = st0 { tsNodes = Map.insert 100 varNode (tsNodes st0) }
            let lookupFunc tid | tid == tidT = return (Just 200)
                               | otherwise = return Nothing
            let (res, _) = runState (substitute lookupFunc 100) st
            res `shouldBe` 200

        it "terminates on recursive types (memoization)" $ do
            -- Node 100: struct List { struct List *next; }
            -- Simplified for substitution test: Node 100 = Ptr(100)
            let ptrNode = AnyRigidNodeF (RReference (Ptr (TargetObject 100)) QUnspecified QNonOwned' (Quals False False))
            let st = st0 { tsNodes = Map.insert 100 ptrNode (tsNodes st0) }
            let (res, _) = runState (substitute (const $ return Nothing) 100) st
            res `shouldBe` 100

    describe "collectRefinableVars" $ do
        it "collects variables from a simple object" $ do
            let tidT = TIdParam PLocal 10 (Just "T")
            let varNode = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let st = st0 { tsNodes = Map.insert 100 varNode (tsNodes st0) }
            let (vars, _) = runState (collectRefinableVars 100) st
            vars `shouldBe` Set.singleton tidT

        it "collects variables from nested structures" $ do
            let tidT = TIdParam PLocal 10 (Just "T")
            let tidU = TIdParam PLocal 11 (Just "U")
            let varT = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let varU = AnyRigidNodeF (RObject (VVar tidU Nothing) (Quals False False))
            let nominalNode = AnyRigidNodeF (RObject (VNominal (dummyL (TIdName "Pair")) [101, 102]) (Quals False False))
            let st = st0 { tsNodes = Map.fromList [(0, AnyRigidNodeF (RTerminal SBottom)), (1, AnyRigidNodeF (RTerminal SAny)), (2, AnyRigidNodeF (RTerminal SConflict)), (101, varT), (102, varU), (103, nominalNode)] }
            let (vars, _) = runState (collectRefinableVars 103) st
            vars `shouldBe` Set.fromList [tidT, tidU]

        it "collects variables from a TargetFunction" $ do
            let tidT = TIdParam PLocal 10 (Just "T")
            let varT = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let funcNode = AnyRigidNodeF (RReference (Ptr (TargetFunction [100] RetVoid)) QUnspecified QNonOwned' (Quals False False))
            let st = st0 { tsNodes = Map.fromList [(0, AnyRigidNodeF (RTerminal SBottom)), (1, AnyRigidNodeF (RTerminal SAny)), (2, AnyRigidNodeF (RTerminal SConflict)), (100, varT), (101, funcNode)] }
            let (vars, _) = runState (collectRefinableVars 101) st
            vars `shouldBe` Set.singleton tidT

        it "does not collect bound variables from an existential" $ do
            -- exists T. T
            let tidT = TIdParam PLocal 10 (Just "T")
                bodyId = 100
                existId = 101
                bodyNode = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
                existNode = AnyRigidNodeF (RObject (VExistential [tidT] bodyId) (Quals False False))
                st = st0 { tsNodes = Map.fromList [(bodyId, bodyNode), (existId, existNode)] }
            let (vars, _) = runState (collectRefinableVars existId) st
            vars `shouldBe` Set.empty

    describe "refreshInstance" $ do
        it "creates fresh variables for refinable parameters" $ do
            let tidT = TIdParam PLocal 10 (Just "T")
            let varNode = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let st = st0 { tsNodes = Map.insert 100 varNode (tsNodes st0) }
            let (nid', st') = runState (refreshInstance Nothing 100) st
            nid' `shouldNotBe` 100
            case Map.lookup nid' (tsNodes st') of
                Just (AnyRigidNodeF (RObject (VVar tid' _) _)) ->
                    tid' `shouldSatisfy` \case { TIdInstance _ -> True; _ -> False }
                _ -> expectationFailure "Expected nid' to be a VVar"

        it "freshens bound variables in an existential" $ do
            -- exists T. T
            let db0 = TIdDeBruijn 0
                bodyId = 100
                existId = 101
                bodyNode = AnyRigidNodeF (RObject (VVar db0 Nothing) (Quals False False))
                existNode = AnyRigidNodeF (RObject (VExistential [db0] bodyId) (Quals False False))
                st = st0 { tsNodes = Map.fromList [(bodyId, bodyNode), (existId, existNode)] }

            let (nid', st') = runState (refreshInstance Nothing existId) st

            -- nid' should be a fresh instance variable
            nid' `shouldNotBe` existId
            case Map.lookup nid' (tsNodes st') of
                Just (AnyRigidNodeF (RObject (VVar (TIdInstance _) _) _)) -> return ()
                _ -> expectationFailure $ "Expected fresh instance variable, got " ++ show (Map.lookup nid' (tsNodes st'))

    describe "refreshSignature" $ do
        it "preserves structural links by using the same skolem hash" $ do
            -- sig: f(T, T) -> T
            let tidT = TIdParam PLocal 10 (Just "T")
            let varNode = AnyRigidNodeF (RObject (VVar tidT Nothing) (Quals False False))
            let st = st0 { tsNodes = Map.insert 100 varNode (tsNodes st0) }
            let ((params', ret, _), _) = runState (refreshSignature [100, 100] (RetVal 100)) st
            case ret of
                RetVal ret' -> do
                    params' !! 0 `shouldBe` params' !! 1
                    params' !! 0 `shouldBe` ret'
                _ -> expectationFailure "Expected RetVal"

    describe "substitutePtrTarget" $ do
        it "substitutes opaque targets when refinable" $ do
            let tidT = TIdParam PLocal 10 (Just "T")
            let target = TargetOpaque tidT
            let lookupFunc tid | tid == tidT = return (Just 200)
                               | otherwise = return Nothing
            let (res, _) = runState (substitutePtrTarget lookupFunc target) st0
            case res of
                TargetObject 200 -> return ()
                _ -> expectationFailure $ "Expected TargetObject 200, got " ++ show res

        it "preserves opaque targets when not refinable" $ do
            let tidT = TIdName "Tox_Core"
            let target = TargetOpaque tidT
            let lookupFunc _ = return (Just 200)
            let (res, _) = runState (substitutePtrTarget lookupFunc target) st0
            res `shouldBe` target

dummyL :: t -> C.Lexeme t
dummyL = C.L (C.AlexPn 0 0 0) C.IdSueType
