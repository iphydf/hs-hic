{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Language.Hic.Refined.TransitionSpec (spec) where

import           Control.Monad.Writer.Strict           (runWriter)
import           Data.Bifunctor                        (first)
import qualified Data.IntMap.Strict                    as IntMap
import qualified Data.List                             as List
import           Data.Map.Strict                       (Map)
import qualified Data.Map.Strict                       as Map
import           Data.Word                             (Word32)
import           Language.Cimple                       (AlexPosn (..),
                                                        Lexeme (..),
                                                        LexemeClass (..))
import           Language.Hic.Refined.Arbitrary        (dummyL)
import           Language.Hic.Refined.Context
import           Language.Hic.Refined.LatticeOp
import           Language.Hic.Refined.PathContext
import           Language.Hic.Refined.Registry
import           Language.Hic.Refined.SemanticEquality
import           Language.Hic.Refined.State
import           Language.Hic.Refined.Transition       (TransitionEnv (..),
                                                        isBot, isNonnull,
                                                        isRefinable, isTop,
                                                        step, variableKey)
import           Language.Hic.Refined.Types
import           Test.Hspec
import           Test.Hspec.QuickCheck                 (prop)
import           Test.QuickCheck                       (Gen, forAll, shuffle,
                                                        (==>))

spec :: Spec
spec = do
    let botID = 0
        anyID = 1
        conflictID = 2
        i32ID = 3
        i32ConstID = 4
        i32Lit0ID = 5
        i32PtrID = 6
        voidPtrID = 7
        voidPtrSkolemID = 17
        voidPtrConstID = 18
        i32ArrID = 8
        funcID = 9
        nomID = 10
        enumID = 11
        varID = 12
        existID = 13
        pointTID = 113
        variantID = 14
        propID = 15
        sizeExprID = 16
        skolemVarID = 19
        skolemVar1ID = 116
        nonnullPtr0ID = 100
        arrBotID = 101
        callbackID = 102
        callbackConstID = 103
        alignPropID = 104
        exist2ID = 105
        pointConstID = 106
        nullPtrTyID = 107
        nonnullNullPtrID = 110
        charID = 111
        variant2ID = 112
        variant12ID = 126
        variant1fID = 127
        funcRetID = 114
        funcRetConstID = 115
        sizeExprCharID = 117
        charPropID = 118
        f32ID = 120
        myCallbackIntID = 121
        myCallbackFloatID = 122
        myCallbackTID = 123
        myCallbackExistID = 124

        dummyL' = L (AlexPn 0 0 0) IdSueType

        nodes = Map.fromList
            [ (botID, AnyRigidNodeF (RTerminal SBottom))
            , (anyID, AnyRigidNodeF (RTerminal SAny))
            , (conflictID, AnyRigidNodeF (RTerminal SConflict))
            , (i32ID, AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False)))
            , (f32ID, AnyRigidNodeF (RObject (VBuiltin F32Ty) (Quals False False)))
            , (i32ConstID, AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals True False)))
            , (i32Lit0ID, AnyRigidNodeF (RObject (VSingleton S32Ty 0) (Quals True True)))
            , (i32PtrID, AnyRigidNodeF (RReference (Ptr (TargetObject i32ID)) QUnspecified QNonOwned' (Quals False False)))
            , (voidPtrID, AnyRigidNodeF (RReference (Ptr (TargetOpaque (TIdName "T"))) QUnspecified QNonOwned' (Quals False False)))
            , (voidPtrSkolemID, AnyRigidNodeF (RReference (Ptr (TargetOpaque (TIdSkolem 752 752 2802))) QUnspecified QNonOwned' (Quals False False)))
            , (voidPtrConstID, AnyRigidNodeF (RReference (Ptr (TargetOpaque (TIdName "T"))) QUnspecified QNonOwned' (Quals True False)))
            , (i32ArrID, AnyRigidNodeF (RReference (Arr i32ID []) QUnspecified QNonOwned' (Quals False False)))
            , (funcID, AnyRigidNodeF (RFunction [i32ID] RetVoid))
            , (nomID, AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Point")) [i32ID, i32ID]) (Quals False False)))
            , (myCallbackIntID, AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "My_Callback")) [i32ID]) (Quals False False)))
            , (myCallbackFloatID, AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "My_Callback")) [f32ID]) (Quals False False)))
            , (myCallbackTID, AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "My_Callback")) [125]) (Quals False False))) -- 125 is VVar TIdDeBruijn 0
            , (myCallbackExistID, AnyRigidNodeF (RObject (VExistential [TIdDeBruijn 0] myCallbackTID) (Quals False False)))
            , (125, AnyRigidNodeF (RObject (VVar (TIdDeBruijn 0) Nothing) (Quals False False)))
            , (enumID, AnyRigidNodeF (RObject (VEnum (dummyL' (TIdName "Color"))) (Quals False False)))
            , (varID, AnyRigidNodeF (RObject (VVar (TIdName "T") Nothing) (Quals False False)))
            , (pointTID, AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Point")) [skolemVarID, skolemVar1ID]) (Quals False False)))
            , (existID, AnyRigidNodeF (RObject (VExistential [TIdDeBruijn 0] pointTID) (Quals False False)))
            , (variantID, AnyRigidNodeF (RObject (VVariant (IntMap.fromList [(1, i32ID)])) (Quals False False)))
            , (propID, AnyRigidNodeF (RObject (VProperty i32ID PSize) (Quals True True)))
            , (sizeExprID, AnyRigidNodeF (RObject (VSizeExpr [(propID, 1)]) (Quals True True)))
            , (skolemVarID, AnyRigidNodeF (RObject (VVar (TIdDeBruijn 0) Nothing) (Quals False False)))
            , (skolemVar1ID, AnyRigidNodeF (RObject (VVar (TIdDeBruijn 1) Nothing) (Quals False False)))
            , (nonnullPtr0ID, AnyRigidNodeF (RReference (Ptr (TargetObject i32Lit0ID)) QNonnull' QNonOwned' (Quals False False)))
            , (arrBotID, AnyRigidNodeF (RReference (Arr botID []) QUnspecified QNonOwned' (Quals False False)))
            , (callbackID, AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Callback")) [i32ID]) (Quals False False)))
            , (callbackConstID, AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Callback")) [i32ConstID]) (Quals False False)))
            , (alignPropID, AnyRigidNodeF (RObject (VProperty i32ID PAlign) (Quals True True)))
            , (exist2ID, AnyRigidNodeF (RObject (VExistential [TIdDeBruijn 0, TIdDeBruijn 1] pointTID) (Quals False False)))
            , (pointConstID, AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Point")) [i32ConstID, i32ConstID]) (Quals False False)))
            , (nullPtrTyID, AnyRigidNodeF (RObject (VBuiltin NullPtrTy) (Quals True True)))
            , (nonnullNullPtrID, AnyRigidNodeF (RReference (Ptr (TargetObject nullPtrTyID)) QNonnull' QNonOwned' (Quals False False)))
            , (charID, AnyRigidNodeF (RObject (VBuiltin S08Ty) (Quals False False)))
            , (variant2ID, AnyRigidNodeF (RObject (VVariant (IntMap.fromList [(2, i32ID)])) (Quals False False)))
            , (variant12ID, AnyRigidNodeF (RObject (VVariant (IntMap.fromList [(1, i32ID), (2, i32ID)])) (Quals False False)))
            , (variant1fID, AnyRigidNodeF (RObject (VVariant (IntMap.fromList [(1, f32ID)])) (Quals False False)))
            , (funcRetID, AnyRigidNodeF (RFunction [i32ID] (RetVal i32ID)))
            , (funcRetConstID, AnyRigidNodeF (RFunction [i32ID] (RetVal i32ConstID)))
            , (sizeExprCharID, AnyRigidNodeF (RObject (VSizeExpr [(charPropID, 1)]) (Quals True True)))
            , (charPropID, AnyRigidNodeF (RObject (VProperty charID PSize) (Quals True True)))
            ]

        registry = Registry $ Map.fromList
            [ ("Point", StructDef (dummyL' "Point") [(TIdParam PGlobal 0 Nothing, Covariant), (TIdParam PGlobal 1 Nothing, Covariant)] [])
            , ("Callback", StructDef (dummyL' "Callback") [(TIdParam PGlobal 0 Nothing, Contravariant)] [])
            , ("My_Callback", StructDef (dummyL' "My_Callback") [(TIdParam PGlobal 0 Nothing, Invariant)] [])
            ]
        pathCtx = PathContext Map.empty Map.empty

        env pol = TransitionEnv nodes registry pol pathCtx emptyPath (botID, anyID, conflictID, botID) True True
        getRes (r, _, _) = r
        isTop' n r d i = fst $ runWriter $ isTop n r d i
        isNonnull' n r d i = fst $ runWriter $ isNonnull n r d i

    describe "isRefinable" $ do
        it "is True for 'T'" $ isRefinable (TIdName "T") `shouldBe` True
        it "is True for 'T1'" $ isRefinable (TIdName "T1") `shouldBe` True
        it "is True for 'T2'" $ isRefinable (TIdName "T2") `shouldBe` True
        it "is False for 'Tox_Core'" $ isRefinable (TIdName "Tox_Core") `shouldBe` False
        it "is True for PGlobal parameters" $ isRefinable (TIdParam PGlobal 0 Nothing) `shouldBe` True

    describe "step" $ do
        context "PJoin (Generalization)" $ do
            it "Bottom join X = X (Rigorous Identity)" $ do
                let ps = ProductState botID i32ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PJoin) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VBuiltin S32Ty) _) -> return ()
                    _ -> expectationFailure $ "Expected i32 node, got " ++ show res

            it "Nonnull meet Bottom = Conflict (Safety violation during Join)" $ do
                -- Joining a Nonnull requirement with a Null state is a contradiction.
                let ps = ProductState nonnullNullPtrID botID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Any join X = Any" $ do
                let ps = ProductState anyID i32ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SAny)

            it "Conflict join X = Conflict (Poisoning)" $ do
                let ps = ProductState conflictID i32ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "i32 join i32 = i32" $ do
                let ps = ProductState i32ID i32ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! i32ID)

            it "i32 join i32Const = i32Const (const)" $ do
                let ps = ProductState i32ID i32ConstID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! i32ConstID)

            it "i32Lit0 join i32 = i32Const (const)" $ do
                let ps = ProductState i32Lit0ID i32ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (const (ps { psNodeL = i32Lit0ID, psNodeR = i32ID })) (nodes Map.! i32ConstID)

            it "i32* join i32* = i32*" $ do
                let ps = ProductState i32PtrID i32PtrID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! i32PtrID)

            it "void* join void* = void*" $ do
                let ps = ProductState voidPtrID voidPtrID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! voidPtrID)

            it "void* const join void* skolem = void* const" $ do
                let ps = ProductState voidPtrConstID voidPtrSkolemID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (const (ps { psNodeL = voidPtrConstID, psNodeR = voidPtrSkolemID })) (nodes Map.! voidPtrConstID)

            it "i32* join void* = void* (refined)" $ do
                let ps = ProductState i32PtrID voidPtrID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe`
                    AnyRigidNodeF (RReference (Ptr (TargetObject (ps { psNodeL = i32ID, psNodeR = i32ID }))) QUnspecified QNonOwned' (Quals False False))

            it "i32[] join i32[] = i32[]" $ do
                let ps = ProductState i32ArrID i32ArrID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! i32ArrID)

            it "func(i32) join func(i32) = func(i32) with contra-pol" $ do
                let ps = ProductState funcID funcID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PJoin) ps emptyRefinements
                res `shouldBe` AnyRigidNodeF (RFunction [ps { psNodeL = i32ID, psNodeR = i32ID, psPolarity = PMeet }] RetVoid)

            it "Point join Point = Point" $ do
                let ps = ProductState nomID nomID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! nomID)

            it "Exist join Exist = Exist with new Gamma" $ do
                let ps = ProductState existID existID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let newGamma = pushMapping 0 emptyContext
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i, psGamma = newGamma, psDepthL = 1, psDepthR = 1 }) (nodes Map.! existID)

            it "Variant(1:i32) join Variant(1:i32) = Variant(1:i32)" $ do
                let ps = ProductState variantID variantID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! variantID)

            it "Variant(1:i32) join Variant(2:i32) = Variant(1:i32, 2:i32)" $ do
                let ps = ProductState variantID variant2ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PJoin) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VVariant m) _) -> do
                        IntMap.keys m `shouldMatchList` [1, 2]
                        let nextL rL rR = ProductState rL rR PJoin False emptyContext 0 0 Nothing Nothing Nothing
                        m IntMap.! 1 `shouldBe` nextL i32ID botID
                        m IntMap.! 2 `shouldBe` nextL botID i32ID
                    _ -> expectationFailure $ "Expected VVariant, got " ++ show res

            it "sizeof(i32) join sizeof(i32) = sizeof(i32)" $ do
                let ps = ProductState propID propID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! propID)

            it "(1*i32) join (1*i32) = (1*i32)" $ do
                let ps = ProductState sizeExprID sizeExprID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! sizeExprID)

            it "Point<i32> join Point<i32Const> = Point<i32Const> (Covariance)" $ do
                let ps = ProductState nomID pointConstID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PJoin) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VNominal _ [p1, p2]) _) -> do
                        psNodeL p1 `shouldBe` i32ID
                        psNodeR p1 `shouldBe` i32ConstID
                        psNodeL p2 `shouldBe` i32ID
                        psNodeR p2 `shouldBe` i32ConstID
                    AnyRigidNodeF (RObject (VExistential [TIdDeBruijn 0, TIdDeBruijn 1] body) _) -> do
                        psNodeL body `shouldBe` nomID
                        psNodeR body `shouldBe` pointTID
                    _ -> expectationFailure $ unlines
                        [ "Expected Nominal or Existential, but got: " ++ show res
                        , "  LHS (psNodeL): " ++ show nomID
                        , "  RHS (psNodeR): " ++ show pointConstID
                        ]

            it "Callback<i32> join Callback<i32Const> = Callback<i32> (Contravariance)" $ do
                let ps = ProductState callbackID callbackConstID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                -- Callback is contravariant, so we meet the parameters. i32 meet i32Const = i32.
                let (res, _, _) = step (env PJoin) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VNominal _ [p]) _) -> do
                        psNodeL p `shouldBe` i32ID
                        psNodeR p `shouldBe` i32ConstID
                        psPolarity p `shouldBe` PMeet
                    _ -> expectationFailure $ "Expected Nominal, got " ++ show res

            it "My_Callback<i32> join My_Callback<f32> = Existential (Promotion)" $ do
                let ps = ProductState myCallbackIntID myCallbackFloatID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PJoin) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VExistential [TIdDeBruijn 0] body) _) -> do
                        psNodeL body `shouldBe` myCallbackIntID
                        psNodeR body `shouldBe` myCallbackTID
                    _ -> expectationFailure $ "Expected Existential, got " ++ show res

            it "refines a variable with multiple incompatible types via nominal join" $ do
                let tid = TIdName "T1"
                    nodeV = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                    vID = 200
                    te = (env PJoin) { teNodes = Map.insert vID nodeV (teNodes (env PJoin)) }

                -- 1. Join My_Callback<i32> with Var
                let ps1 = ProductState myCallbackIntID vID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (_, refs1, _) = step te ps1 emptyRefinements
                -- Var should be refined to My_Callback<i32>
                getRefinement (variableKey (teNodes te) 0 tid) refs1 `shouldBe` Just myCallbackIntID

                -- 2. Join My_Callback<f32> with Var (which is now My_Callback<i32>)
                let ps2 = ProductState myCallbackFloatID vID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (res2, _, _) = step te ps2 refs1
                -- This should result in existential promotion!
                case res2 of
                    AnyRigidNodeF (RObject (VExistential _ _) _) -> return ()
                    _ -> expectationFailure $ "Expected Existential, got " ++ show res2

            it "sizeof(i32) join alignof(i32) = Top (Mismatch)" $ do
                let ps = ProductState propID alignPropID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Exist(1) join Exist(2) = Top (Binder mismatch)" $ do
                let ps = ProductState existID exist2ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Function Return Covariance: PJoin(Ret i32, Ret i32Const) = Ret i32Const" $ do
                let ps = ProductState funcRetID funcRetConstID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PJoin) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RFunction _ (RetVal retPS)) -> do
                        psNodeL retPS `shouldBe` i32ID
                        psNodeR retPS `shouldBe` i32ConstID
                        psPolarity retPS `shouldBe` PJoin
                    _ -> expectationFailure $ "Expected RFunction with RetVal, got " ++ show res

            it "SizeExpr Mismatch: PJoin(sizeof i32, alignof i32) = Top" $ do
                let ps = ProductState propID alignPropID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Refinement: refines a variable when joining with a concrete type (PJoin)" $ do
                let tid = TIdSkolem 10 20 0
                    nodeQ = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                    nodeInt = AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))
                    qID = 100
                    intID = 101
                    te = (env PJoin) { teNodes = Map.insert qID nodeQ (Map.insert intID nodeInt (teNodes (env PJoin))) }
                    ps = ProductState qID intID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                let (_, refs, _) = step te ps emptyRefinements
                getRefinement (variableKey (teNodes te) 0 tid) refs `shouldBe` Just intID

            it "implements indirection collapse when variable is involved" $ do
                let tid = TIdInstance 100
                    nodeV = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                    vID = 1000
                    -- ptrToBot is a pointer that was refined to SBottom
                    ptrToBotID = botID
                    te = (env PMeet) { teNodes = Map.insert vID nodeV (teNodes (env PMeet)) }
                    ps1 = ProductState vID ptrToBotID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                -- First step: refine variable v to SBottom
                let (_, refs1, _) = step te ps1 emptyRefinements
                getRefinement (variableKey (teNodes te) 0 tid) refs1 `shouldBe` Just ptrToBotID

                -- Second step: meet Nonnull pointer with the refined variable (which is now SBottom)
                let nonnullID = nonnullPtr0ID
                    ps2 = ProductState nonnullID vID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step te ps2 refs1) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

        context "PMeet (Refinement)" $ do
            it "Bottom meet X = Bottom" $ do
                let ps = ProductState botID i32ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SBottom)

            it "Any meet X = X (Identity)" $ do
                let ps = ProductState anyID i32ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PMeet) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VBuiltin S32Ty) _) -> return ()
                    _ -> expectationFailure $ "Expected i32 node, got " ++ show res

            it "Conflict meet X = Conflict (Poisoning)" $ do
                let ps = ProductState conflictID i32ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Nonnull ptr to nullptr = Conflict (Nullability contradiction)" $ do
                let ps = ProductState nonnullNullPtrID nonnullNullPtrID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Arr(Bottom) = Bottom (Indirection collapse)" $ do
                let ps = ProductState arrBotID arrBotID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SBottom)

            it "Ptr(Bottom) = Bottom (Indirection collapse)" $ do
                let ptrBot = AnyRigidNodeF (RReference (Ptr (TargetObject botID)) QUnspecified QNonOwned' (Quals False False))
                    idPtrBot = 200
                    te = (env PMeet) { teNodes = Map.insert idPtrBot ptrBot (teNodes (env PMeet)) }
                    ps = ProductState idPtrBot idPtrBot PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step te ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SBottom)

            it "Nonnull meet Bottom = Conflict (Witness Contradiction)" $ do
                -- nonnullNullPtrID is Nonnull. botID is SBottom.
                let ps = ProductState nonnullNullPtrID botID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Refined Nonnull meet Bottom = Conflict" $ do
                let tid = TIdSkolem 10 20 0
                    nodeQ = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                    qID = 100
                    -- Pre-refine qID to a Nonnull pointer
                    refs = setRefinement (variableKey nodes 0 tid) nonnullNullPtrID emptyRefinements
                    te = (env PMeet) { teNodes = Map.insert qID nodeQ nodes }
                    ps = ProductState qID botID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step te ps refs) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Dereferencing Bottom = Conflict" $ do
                -- Mimics *p where p is SBottom. Dereferencing implies a Nonnull requirement.
                let ps = ProductState nonnullPtr0ID botID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "i32 meet i32Const = i32 (mutable refinement)" $ do
                let ps = ProductState i32ID i32ConstID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! i32ID)

            it "Inherent Constancy: PMeet(Inherent Const, Mutable) = Conflict" $ do
                -- This test showcases the need for qPhysical.
                -- Currently, we use VSingleton to mimic physical constancy,
                -- but we need it for VBuiltin as well (for global consts).
                let ps = ProductState i32Lit0ID i32ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Issue: meeting const VBuiltin with mutable results in mutable (unsound for globals)" $ do
                -- i32ConstID is RObject (VBuiltin S32Ty) (Quals True True)
                -- i32ID is RObject (VBuiltin S32Ty) (Quals False False)
                let ps = ProductState i32ConstID i32ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PMeet) ps emptyRefinements
                -- Currently this results in i32ID (mutable), which we want to change for globals.
                res `shouldBe` fmap (\i -> ps { psNodeL = i, psNodeR = i }) (nodes Map.! i32ID)

            it "refines tid 'T' (identity)" $ do
                let tid = TIdName "T"
                    nodeQ = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                    nodeInt = AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))
                    qID = 2000
                    intID = 2001
                    te = (env PMeet) { teNodes = Map.insert qID nodeQ (Map.insert intID nodeInt (teNodes (env PMeet))) }
                    ps = ProductState qID intID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (_, refs, _) = step te ps emptyRefinements
                getRefinement (variableKey (teNodes te) 0 tid) refs `shouldBe` Just intID

            it "refines T1 variable (Rank-1 Poly-variance)" $ do
                let tid = TIdName "T1"
                    nodeQ = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                    nodeInt = AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))
                    qID = 2000
                    intID = 2001
                    te = (env PMeet) { teNodes = Map.insert qID nodeQ (Map.insert intID nodeInt (teNodes (env PMeet))) }
                    ps = ProductState qID intID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (_, refs, _) = step te ps emptyRefinements
                getRefinement (variableKey (teNodes te) 0 tid) refs `shouldBe` Just intID

            it "refines PGlobal template parameters (Whole-Program Analysis)" $ do
                let tid = TIdParam PGlobal 0 (Just "userdata")
                    nodeQ = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                    nodeInt = AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))
                    qID = 3000
                    intID = 3001
                    te = (env PMeet) { teNodes = Map.insert qID nodeQ (Map.insert intID nodeInt (teNodes (env PMeet))) }
                    ps = ProductState qID intID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, refs, _) = step te ps emptyRefinements
                res `shouldNotBe` AnyRigidNodeF (RTerminal SConflict)
                getRefinement (variableKey (teNodes te) 0 tid) refs `shouldBe` Just intID

            it "demonstrates one-way refinement using teRefineR = False" $ do
                let tidL = TIdName "T1"
                    tidR = TIdName "T"
                    nodeL = AnyRigidNodeF (RObject (VVar tidL Nothing) (Quals False False))
                    nodeR = AnyRigidNodeF (RObject (VVar tidR Nothing) (Quals False False))
                    idL = 2004
                    idR = 2005
                    te = (env PMeet) { teNodes = Map.insert idL nodeL (Map.insert idR nodeR (teNodes (env PMeet)))
                                     , teRefineR = False }
                    ps = ProductState idL idR PMeet False emptyContext 0 0 Nothing Nothing Nothing

                -- Simulate that T1 is already refined to Int
                let idI32 = i32ID
                let refs1 = setRefinement (variableKey (teNodes te) 0 tidL) idI32 emptyRefinements

                let (_, refs2, _) = step te ps refs1
                -- We want T NOT to be refined to Int (one-way refinement)
                getRefinement (variableKey (teNodes te) 0 tidR) refs2 `shouldBe` Nothing

            it "results in concrete type when meeting with non-refinable variable (one-way)" $ do
                let tidR = TIdName "T"
                    nodeR = AnyRigidNodeF (RObject (VVar tidR Nothing) (Quals False False))
                    idInt = i32ID
                    idR = 2005
                    te = (env PMeet) { teNodes = Map.insert idR nodeR (teNodes (env PMeet))
                                     , teRefineR = False }
                    ps = ProductState idInt idR PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step te ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VBuiltin S32Ty) _) -> return ()
                    _ -> expectationFailure $ "Expected i32 node, got " ++ show res

            it "Refinement Conflict: persistent refinement A meet B = Top if A /= B" $ do
                let tid = TIdSkolem 10 20 0
                    nodeQ = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                    qID = 100
                    te = (env PMeet) { teNodes = Map.insert qID nodeQ (teNodes (env PMeet)) }
                    ps = ProductState qID charID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                    -- Pre-refine tid to i32ID
                    refs = setRefinement (variableKey (teNodes te) 0 tid) i32ID emptyRefinements
                getRes (step te ps refs) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Physical Constancy: PMeet(Literal, Mutable) = Top" $ do
                -- i32Lit0ID is physically const (Quals True True)
                -- i32ID is mutable (Quals False False)
                let ps = ProductState i32Lit0ID i32ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Variant Mismatch: PMeet(Variant1, Variant2) = Top" $ do
                let ps = ProductState variantID variant2ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Variant(1:i32, 2:i32) meet Variant(1:i32) = Variant(1:i32)" $ do
                let ps = ProductState variant12ID variantID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PMeet) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VVariant m) _) -> do
                        IntMap.keys m `shouldMatchList` [1]
                        let nextL rL rR = ProductState rL rR PMeet False emptyContext 0 0 Nothing Nothing Nothing
                        m IntMap.! 1 `shouldBe` nextL i32ID i32ID
                    _ -> expectationFailure $ "Expected VVariant, got " ++ show res

            it "Variant(1:i32) meet Variant(1:f32) = Variant(1:Conflict)" $ do
                let ps = ProductState variantID variant1fID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PMeet) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VVariant m) _) -> do
                        IntMap.keys m `shouldMatchList` [1]
                        let nextL rL rR = ProductState rL rR PMeet False emptyContext 0 0 Nothing Nothing Nothing
                        m IntMap.! 1 `shouldBe` nextL i32ID f32ID
                    _ -> expectationFailure $ "Expected VVariant, got " ++ show res

            it "SizeExpr Mismatch: PMeet(sizeof i32, alignof i32) = Top" $ do
                let ps = ProductState propID alignPropID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Function Return Meet: PMeet(Ret i32, Ret i32Const) = Ret i32" $ do
                let ps = ProductState funcRetID funcRetConstID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PMeet) ps emptyRefinements
                case res of
                    AnyRigidNodeF (RFunction _ (RetVal retPS)) -> do
                        psNodeL retPS `shouldBe` i32ID
                        psNodeR retPS `shouldBe` i32ConstID
                        psPolarity retPS `shouldBe` PMeet
                    _ -> expectationFailure $ "Expected RFunction with RetVal, got " ++ show res

            it "allows meeting two refinable TargetOpaque nodes and unifies them structurally" $ do
                let tidL = TIdSkolem 10 20 1
                    tidR = TIdSkolem 30 40 2
                    ptrL = AnyRigidNodeF (RReference (Ptr (TargetOpaque tidL)) QUnspecified QNonOwned' (Quals False False))
                    ptrR = AnyRigidNodeF (RReference (Ptr (TargetOpaque tidR)) QUnspecified QNonOwned' (Quals False False))
                    idL = 2002
                    idR = 2003
                    te = (env PMeet) { teNodes = Map.insert idL ptrL (Map.insert idR ptrR (teNodes (env PMeet))) }
                    ps = ProductState idL idR PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step te ps emptyRefinements
                case res of
                    AnyRigidNodeF (RReference (Ptr (TargetOpaque tid)) _ _ _) ->
                        tid `shouldBe` min tidL tidR
                    _ -> expectationFailure $ "Expected TargetOpaque, got " ++ show res

        context "Bugs and Critical Mistakes" $ do
            it "Issue 1: Mutable Literal Assignment (correctly forbidden in Strict Hic)" $ do
                let ps = ProductState i32ID i32Lit0ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (res, _, _) = step (env PMeet) ps emptyRefinements
                res `shouldBe` AnyRigidNodeF (RTerminal SConflict)

            it "Issue 4: Asymmetric depth shifting in Packing Rule (PJoin)" $ do
                let db0 = TIdDeBruijn 0
                    nodeVar = AnyRigidNodeF (RObject (VVar db0 Nothing) (Quals False False))
                    idVarL = 5000
                    idExistInnerR = 5004
                    nodes' = Map.insert idVarL nodeVar $ Map.insert idExistInnerR (AnyRigidNodeF (RObject (VExistential [db0] 2) (Quals False False))) nodes
                    te = (env PJoin) { teNodes = nodes' }
                    ps = ProductState idVarL idExistInnerR PJoin False (pushMapping 0 emptyContext) 1 1 Nothing Nothing Nothing
                let (res, _, _) = step te ps emptyRefinements
                case res of
                    AnyRigidNodeF (RObject (VExistential _ childPS) _) -> do
                        -- The left side was concrete, it stays at depth 1
                        psDepthL childPS `shouldBe` 1
                        -- The right side was an Existential, it shifts to depth 2
                        psDepthR childPS `shouldBe` 2
                    _ -> expectationFailure $ "Expected Existential, got " ++ show res

            it "allows meeting RObject(VVar) with RReference (Refinement identity)" $ do
                let ps = ProductState varID i32PtrID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                let (result, _, _) = step (env PMeet) ps emptyRefinements
                result `shouldNotBe` AnyRigidNodeF (RTerminal SConflict)

            it "SizeExpr Mismatch: PJoin(sizeof i32, alignof i32) = Top" $ do
                let ps = ProductState propID alignPropID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

    describe "Numeric Decay (Information Erasure)" $ do
        context "VProperty decay" $ do
            it "PJoin(VProperty, VBuiltin) decays to VBuiltin" $ do
                let ps = ProductState propID i32ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals True False))

            it "PMeet(VProperty, VBuiltin) decays to VBuiltin (Value satisfies requirement)" $ do
                let ps = ProductState propID i32ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))

            it "PMeet(VBuiltin, VProperty) results in Conflict (Integer cannot satisfy symbolic requirement)" $ do
                let ps = ProductState i32ID propID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

        context "VSizeExpr decay" $ do
            it "PJoin(VSizeExpr, VBuiltin) decays to VBuiltin" $ do
                let ps = ProductState sizeExprID i32ID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PJoin) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals True False))

            it "PMeet(VSizeExpr, VBuiltin) decays to VBuiltin" $ do
                let ps = ProductState sizeExprID i32ID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))

            it "PMeet(VBuiltin, VSizeExpr) results in Conflict" $ do
                let ps = ProductState i32ID sizeExprID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                getRes (step (env PMeet) ps emptyRefinements) `shouldBe` AnyRigidNodeF (RTerminal SConflict)

    describe "Size Expression Incompleteness" $ do
        it "fails to unify semantically identical but physically distinct size expressions" $ do
            -- Size expression A: sizeof(i32)
            -- Size expression B: sizeof(i32)
            -- These are semantically identical (both refer to S32Ty size)
            -- but the VProperty nodes have different physical IDs.

            let propA_ID = 200
                propB_ID = 201
                sizeA_ID = 202
                sizeB_ID = 203

                nodes' = Map.fromList
                    [ (botID, AnyRigidNodeF (RTerminal SBottom))
                    , (anyID, AnyRigidNodeF (RTerminal SAny))
                    , (conflictID, AnyRigidNodeF (RTerminal SConflict))
                    , (i32ID, AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False)))
                    , (propA_ID, AnyRigidNodeF (RObject (VProperty i32ID PSize) (Quals True True)))
                    , (propB_ID, AnyRigidNodeF (RObject (VProperty i32ID PSize) (Quals True True)))
                    , (sizeA_ID, AnyRigidNodeF (RObject (VSizeExpr [(propA_ID, 1)]) (Quals True True)))
                    , (sizeB_ID, AnyRigidNodeF (RObject (VSizeExpr [(propB_ID, 1)]) (Quals True True)))
                    ]

            -- Regression: Unify expressions with semantically identical properties
            -- but distinct physical IDs and differing list orders.
            -- Semantic Sort: Prop(char) < Prop(i32)
            -- Physical Sort: ID(i32) < ID(char)

            let propI32_A = 210
                propChar_A = 211
                propI32_B = 205 -- Reverse physical order
                propChar_B = 204

                sizeA_ID' = 212
                sizeB_ID' = 213

                nodes'' = Map.fromList
                    [ (i32ID, AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False)))
                    , (charID, AnyRigidNodeF (RObject (VBuiltin S08Ty) (Quals False False)))
                    , (propI32_A, AnyRigidNodeF (RObject (VProperty i32ID PSize) (Quals True True)))
                    , (propChar_A, AnyRigidNodeF (RObject (VProperty charID PSize) (Quals True True)))
                    , (propI32_B, AnyRigidNodeF (RObject (VProperty i32ID PSize) (Quals True True)))
                    , (propChar_B, AnyRigidNodeF (RObject (VProperty charID PSize) (Quals True True)))
                    -- sizeA: [(210, 1), (211, 1)] -> Sorted by ID: [210, 211] (i32, char)
                    , (sizeA_ID', AnyRigidNodeF (RObject (VSizeExpr [(propI32_A, 1), (propChar_A, 1)]) (Quals True True)))
                    -- sizeB: [(204, 1), (205, 1)] -> Sorted by ID: [204, 205] (char, i32)
                    , (sizeB_ID', AnyRigidNodeF (RObject (VSizeExpr [(propChar_B, 1), (propI32_B, 1)]) (Quals True True)))
                    ]

                env'' = TransitionEnv (Map.union nodes'' nodes') registry PJoin pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps'' = ProductState sizeA_ID' sizeB_ID' PJoin False emptyContext 0 0 Nothing Nothing Nothing

            -- Physical sort A: [(210, i32), (211, char)]
            -- Physical sort B: [(204, char), (205, i32)]
            -- zipWith pairs (i32, char) and (char, i32).
            -- BUT aggS checks semantic equality first.
            -- Semantic sort A: [(char, 1), (i32, 1)]
            -- Semantic sort B: [(char, 1), (i32, 1)]
            -- aggS says they are semantically equal.
            -- THEN aggS' sorts physically and zips.
            -- It will pair (propI32_A, propChar_B) and (propChar_A, propI32_B).
            -- This results in a VSizeExpr that is semantically WRONG!
            -- Because it pairs different properties.

            let (res, _, _) = step env'' ps'' emptyRefinements
            case res of
                AnyRigidNodeF (RObject (VSizeExpr final) _) -> do
                    -- final should contain (ProductState propChar_A propChar_B) and (ProductState propI32_A propI32_B)
                    -- but it will contain (ProductState propI32_A propChar_B) and (ProductState propChar_A propI32_B)
                    let isCharPair (p, _) = psNodeL p == propChar_A && psNodeR p == propChar_B
                    any isCharPair final `shouldBe` True
                _ -> expectationFailure $ "Expected VSizeExpr, got " ++ show res

    describe "Universal Properties" $ do
        prop "Idempotence: step(pol, X, X) semantically X" $ \pol (nodeX :: AnyRigidNodeF TemplateId Word32) ->
            let isPhys (AnyRigidNodeF (RObject s q)) = not (qConst q) && case s of
                    VSingleton{}       -> True
                    VBuiltin NullPtrTy -> True
                    VProperty{}        -> True
                    _                  -> False
                isPhys _ = False
            in not (isPhys nodeX) ==>
                let nodes' = Map.fromList [(2, nodeX)]
                    env' = TransitionEnv nodes' registry pol pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                    ps = ProductState 2 2 pol False emptyContext 0 0 Nothing Nothing Nothing
                    (res, _, _) = step env' ps emptyRefinements
                in semEqStep res psNodeL nodeX

        prop "Commutativity: step(pol, L, R) == swap(step(pol, R, L))" $ \pol (nodeL :: AnyRigidNodeF TemplateId Word32) (nodeR :: AnyRigidNodeF TemplateId Word32) ->
            let isSymbolic (AnyRigidNodeF (RObject s _)) = case s of
                    VProperty{} -> True
                    VSizeExpr{} -> True
                    _           -> False
                isSymbolic _ = False
                isPhysical (AnyRigidNodeF (RObject s _)) = case s of
                    VBuiltin bt     -> bt /= NullPtrTy
                    VSingleton bt _ -> bt /= NullPtrTy
                    _               -> False
                isPhysical _ = False
                -- Commutativity is broken for mixed Symbolic/Physical PMeet operations (Intentional Decay).
                -- As defined in doc/numeric-decay.md, the transition is a "reductive transformation":
                --   Symbolic ⊓ Physical = Physical (Decay)
                --   Physical ⊓ Symbolic = Conflict (Hardening)
                -- This directional behavior preserves safety in hardened contexts while allowing
                -- flexible assignment to generic integer variables.
                isMixedMeet = pol == PMeet &&
                              ((isSymbolic nodeL && isPhysical nodeR) ||
                               (isPhysical nodeL && isSymbolic nodeR))
            in not isMixedMeet ==>
                let nodes' = Map.fromList [(2, nodeL), (3, nodeR)]
                    env' = TransitionEnv nodes' registry pol pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                    swapStepResult (AnyRigidNodeF n) = AnyRigidNodeF (fmap swapPS n)
                    swapPS ps = ps { psNodeL = psNodeR ps, psNodeR = psNodeL ps, psDepthL = psDepthR ps, psDepthR = psDepthL ps }
                    psL = ProductState 2 3 pol False emptyContext 0 0 Nothing Nothing Nothing
                    psR = ProductState 3 2 pol False emptyContext 0 0 Nothing Nothing Nothing
                    resL = getRes $ step env' psL emptyRefinements
                    resR = getRes $ step env' psR emptyRefinements
                in semEqResult resL (swapStepResult resR)

        prop "Identity for PJoin: step(PJoin, X, Bottom) == X" $ \nodeX ->
            let nodes' = Map.fromList [(botID, AnyRigidNodeF (RTerminal SBottom)), (anyID, AnyRigidNodeF (RTerminal SAny)), (conflictID, AnyRigidNodeF (RTerminal SConflict)), (3, nodeX)]
                env' = TransitionEnv nodes' registry PJoin pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 3 botID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                res = getRes (step env' ps emptyRefinements)
                -- Map nodeX to use identical product states for identity comparison
                expectedResult = fmap (\i -> ProductState i i PJoin False emptyContext 0 0 Nothing Nothing Nothing) nodeX
            in if isTop' nodes' emptyRefinements 0 3
               then res == AnyRigidNodeF (RTerminal SConflict)
               else semEqResult res expectedResult

        prop "Zero for PJoin: step(PJoin, X, Any) == Any or Conflict" $ \nodeX ->
            let nodes' = Map.fromList [(botID, AnyRigidNodeF (RTerminal SBottom)), (anyID, AnyRigidNodeF (RTerminal SAny)), (conflictID, AnyRigidNodeF (RTerminal SConflict)), (3, nodeX)]
                env' = TransitionEnv nodes' registry PJoin pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 3 anyID PJoin False emptyContext 0 0 Nothing Nothing Nothing
                res = getRes (step env' ps emptyRefinements)
            in if isTop' nodes' emptyRefinements 0 3
               then res == AnyRigidNodeF (RTerminal SConflict)
               else res == AnyRigidNodeF (RTerminal SAny)

        prop "Identity for PMeet: step(PMeet, X, Any) == X" $ \nodeX ->
            let nodes' = Map.fromList [(botID, AnyRigidNodeF (RTerminal SBottom)), (anyID, AnyRigidNodeF (RTerminal SAny)), (conflictID, AnyRigidNodeF (RTerminal SConflict)), (3, nodeX)]
                env' = TransitionEnv nodes' registry PMeet pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 3 anyID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                res = getRes (step env' ps emptyRefinements)
                expectedResult = fmap (\i -> ProductState i i PMeet False emptyContext 0 0 Nothing Nothing Nothing) nodeX
            in if isTop' nodes' emptyRefinements 0 3
               then res == AnyRigidNodeF (RTerminal SConflict)
               else semEqResult res expectedResult

        prop "Poisoning for PJoin: step(PJoin, X, Conflict) == Conflict" $ \nodeX ->
            let nodes' = Map.fromList [(conflictID, AnyRigidNodeF (RTerminal SConflict)), (3, nodeX)]
                env' = TransitionEnv nodes' registry PJoin pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 3 conflictID PJoin False emptyContext 0 0 Nothing Nothing Nothing
            in getRes (step env' ps emptyRefinements) == AnyRigidNodeF (RTerminal SConflict)

        prop "Poisoning for PMeet: step(PMeet, X, Conflict) == Conflict" $ \nodeX ->
            let nodes' = Map.fromList [(conflictID, AnyRigidNodeF (RTerminal SConflict)), (3, nodeX)]
                env' = TransitionEnv nodes' registry PMeet pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 3 conflictID PMeet False emptyContext 0 0 Nothing Nothing Nothing
            in getRes (step env' ps emptyRefinements) == AnyRigidNodeF (RTerminal SConflict)

        prop "Zero for PMeet: step(PMeet, X, Bottom) == Bottom or Conflict (Safety Algebra)" $ \nodeX ->
            let nodes' = Map.fromList [(botID, AnyRigidNodeF (RTerminal SBottom)), (anyID, AnyRigidNodeF (RTerminal SAny)), (conflictID, AnyRigidNodeF (RTerminal SConflict)), (3, nodeX)]
                env' = TransitionEnv nodes' registry PMeet pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 3 botID PMeet False emptyContext 0 0 Nothing Nothing Nothing
                res = getRes (step env' ps emptyRefinements)
                expected = if isTop' nodes' emptyRefinements 0 3 || isNonnull' nodes' emptyRefinements 0 3 then AnyRigidNodeF (RTerminal SConflict) else AnyRigidNodeF (RTerminal SBottom)
            in res == expected

        prop "NullPtr Collapse: Reference(NullPtrTy) collapses to SBottom" $ \pol ->
            let node = AnyRigidNodeF (RReference (Ptr (TargetObject nullPtrTyID)) QUnspecified QNonOwned' (Quals False False))
                nodes' = Map.fromList [(2, node), (nullPtrTyID, nodes Map.! nullPtrTyID)]
                env' = TransitionEnv nodes' registry pol pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 2 2 pol False emptyContext 0 0 Nothing Nothing Nothing
            in getRes (step env' ps emptyRefinements) == AnyRigidNodeF (RTerminal SBottom)

        prop "Nominal Mismatch: step(pol, Nominal A, Nominal B) == Top if A /= B" $ \pol ->
            let nodeA = AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Point")) []) (Quals False False))
                nodeB = AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Callback")) []) (Quals False False))
                nodes' = Map.fromList [(2, nodeA), (3, nodeB)]
                env' = TransitionEnv nodes' registry pol pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 2 3 pol False emptyContext 0 0 Nothing Nothing Nothing
            in getRes (step env' ps emptyRefinements) == AnyRigidNodeF (RTerminal SConflict)

        prop "Polarity Inversion: Function arguments flip polarity" $ \pol ->
            let nodeF = AnyRigidNodeF (RFunction [i32ID] RetVoid)
                nodes' = Map.fromList [(1000, nodeF), (i32ID, nodes Map.! i32ID)]
                env' = TransitionEnv nodes' registry pol pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 1000 1000 pol False emptyContext 0 0 Nothing Nothing Nothing
                (res, _, _) = step env' ps emptyRefinements
            in case res of
                AnyRigidNodeF (RFunction [argPS] _) ->
                    psPolarity argPS == (if pol == PJoin then PMeet else PJoin)
                _ -> False

        prop "Qualifier Monotonicity: join(Const, Mutable) == Const, meet(Const, Mutable) == Mutable" $ \pol ->
            let nodeM = AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))
                nodeC = AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals True False))
                nodes' = Map.fromList [(2, nodeM), (3, nodeC)]
                env' = TransitionEnv nodes' registry pol pathCtx emptyPath (botID, anyID, conflictID, botID) True True
                ps = ProductState 2 3 pol False emptyContext 0 0 Nothing Nothing Nothing
                (res, _, _) = step env' ps emptyRefinements
            in case res of
                AnyRigidNodeF (RObject _ q) ->
                    qConst q == (if pol == PJoin then True else False)
                _ -> False

    describe "Packing Rule (Existential Promotion)" $ do
        it "does NOT unify parameters during promotion join" $ do
            -- My_Callback<T1> join My_Callback<T2>
            let tid1 = TIdName "T1"
                tid2 = TIdName "T2"
                nodeV1 = AnyRigidNodeF (RObject (VVar tid1 Nothing) (Quals False False))
                nodeV2 = AnyRigidNodeF (RObject (VVar tid2 Nothing) (Quals False False))
                vID1 = 300
                vID2 = 301
                -- 302: My_Callback<T1>
                -- 303: My_Callback<T2>
                nodeMC1 = AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "My_Callback")) [vID1]) (Quals False False))
                nodeMC2 = AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "My_Callback")) [vID2]) (Quals False False))
                mcID1 = 302
                mcID2 = 303
                te = (env PJoin) { teNodes = Map.fromList
                                     [ (vID1, nodeV1), (vID2, nodeV2)
                                     , (mcID1, nodeMC1), (mcID2, nodeMC2)
                                     , (124, nodes Map.! 124), (123, nodes Map.! 123), (125, nodes Map.! 125) -- Existential nodes
                                     ] }
                ps = ProductState mcID1 mcID2 PJoin False emptyContext 0 0 Nothing Nothing Nothing

            let (res, refs, _) = step te ps emptyRefinements

            -- 1. Result should be the existential
            case res of
                AnyRigidNodeF (RObject (VExistential _ _) _) -> return ()
                _ -> expectationFailure $ "Expected Existential, got " ++ show res

            -- 2. T1 and T2 must NOT be refined (unified)
            getRefinement (variableKey (teNodes te) 0 tid1) refs `shouldBe` Nothing
            getRefinement (variableKey (teNodes te) 0 tid2) refs `shouldBe` Nothing

        it "promotes My_Callback<i32> join My_Callback<f32> to exists T. My_Callback<T>" $ do
            let ps = ProductState 121 122 PJoin False emptyContext 0 0 Nothing Nothing Nothing
            let (res, _, _) = step (env PJoin) ps emptyRefinements
            case res of
                AnyRigidNodeF (RObject (VExistential [TIdDeBruijn 0] body) _) -> do
                    -- Verify structural correspondence
                    psNodeL body `shouldBe` 121
                    psNodeR body `shouldBe` 123
                _ -> expectationFailure $ "Expected promotion to VExistential, got " ++ show res

        it "refines a variable to the promoted existential supertype during PJoin" $ do
            let tid = TIdName "T1"
                nodeV = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
                vID = 200
                te = (env PJoin) { teNodes = Map.insert vID nodeV (teNodes (env PJoin)) }

            -- Simulate T1 is already refined to My_Callback<int> (node 121)
            let refs1 = setRefinement (variableKey (teNodes te) 0 tid) 121 emptyRefinements

            -- Join My_Callback<float> (node 122) with T1 (refined to 121)
            let ps = ProductState 122 vID PJoin False emptyContext 0 0 Nothing Nothing Nothing
            let (res, refs2, _) = step te ps refs1

            -- Verify we got the promotion result
            case res of
                AnyRigidNodeF (RObject (VExistential _ _) _) -> return ()
                _ -> expectationFailure $ "Expected Existential result, got " ++ show res

            -- T1 should be updated to 124 (exists T. My_Callback<T>)
            getRefinement (variableKey (teNodes te) 0 tid) refs2 `shouldBe` Just 124

    describe "Bound Variable Isolation" $ do
        it "does not refine TIdDeBruijn variables (bound variables) in MappingRefinements" $ do
            -- Bound variables must not be refined globally.
            -- Joining a bound variable (DeBruijn 0) with a concrete type (i32)
            -- should result in SAny and NO refinements.
            let db0 = TIdDeBruijn 0
                nodeV = AnyRigidNodeF (RObject (VVar db0 Nothing) (Quals False False))
                idV = 300
                te = (env PJoin) { teNodes = Map.insert idV nodeV (teNodes (env PJoin)) }
                ps = ProductState idV i32ID PJoin False emptyContext 0 0 Nothing Nothing Nothing

            let (res, refs, _) = step te ps emptyRefinements

            -- 1. Result should be Top (Join of different categories/un-unified variables)
            res `shouldBe` AnyRigidNodeF (RTerminal SAny)

            -- 2. MappingRefinements must remain empty
            mrRefinements refs `shouldBe` IntMap.empty

    describe "One-Way Inheritance (psOneWay)" $ do
        it "prevents refining R when oneWay is True" $ do
            let tidL = TIdName "T1" -- Refinable
                tidR = TIdName "T2" -- Refinable
                nodeL = AnyRigidNodeF (RObject (VVar tidL Nothing) (Quals False False))
                nodeR = AnyRigidNodeF (RObject (VVar tidR Nothing) (Quals False False))
                idL = 400
                idR = 401
                te = (env PMeet) { teNodes = Map.fromList [(idL, nodeL), (idR, nodeR)], teRefineR = False }
                -- oneWay = True
                ps = ProductState idL idR PMeet True emptyContext 0 0 Nothing Nothing Nothing

            -- Meeting two variables with oneWay=True should NOT unify them.
            -- It should return L and NOT refine R.
            let (res, refs, _) = step te ps emptyRefinements

            case res of
                AnyRigidNodeF (RObject (VVar t _) _) -> t `shouldBe` tidL
                _ -> expectationFailure $ "Expected VVar L, got " ++ show res

            getRefinement (variableKey (teNodes te) 0 tidR) refs `shouldBe` Nothing

        it "allows refining L from a concrete R when oneWay is True" $ do
            let tidL = TIdName "T1" -- Refinable
                nodeL = AnyRigidNodeF (RObject (VVar tidL Nothing) (Quals False False))
                idL = 400
                te = (env PMeet) { teNodes = Map.insert idL nodeL (teNodes (env PMeet)), teRefineR = False }
                ps = ProductState idL i32ID PMeet True emptyContext 0 0 Nothing Nothing Nothing

            -- Meeting L with i32 should refine L to i32
            let (_, refs, _) = step te ps emptyRefinements

            getRefinement (variableKey (teNodes te) 0 tidL) refs `shouldBe` Just i32ID

    describe "Location-Invariant Matching" $ do
        it "promotes VNominal types with different lexeme locations" $ do
            let tid = TIdName "My_Callback"
                -- Different AlexPn locations
                l1 = L (AlexPn 10 1 10) IdSueType tid
                l2 = L (AlexPn 20 2 20) IdSueType tid
                node1 = AnyRigidNodeF (RObject (VNominal l1 [3]) (Quals False False))
                node2 = AnyRigidNodeF (RObject (VNominal l2 [120]) (Quals False False))
                id1 = 500
                id2 = 501
                te = (env PJoin) { teNodes = Map.union (Map.fromList [(id1, node1), (id2, node2)]) (teNodes (env PJoin)) }
                ps = ProductState id1 id2 PJoin False emptyContext 0 0 Nothing Nothing Nothing

            -- Should trigger promotion despite different source locations
            let (res, _, _) = step te ps emptyRefinements
            case res of
                AnyRigidNodeF (RObject (VExistential _ _) _) -> return ()
                _ -> expectationFailure $ "Expected Promotion to Existential, got " ++ show res
