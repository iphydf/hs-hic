{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.TypeSystem.Core.LatticeSpec (spec) where

import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import           Data.Fix                                      (Fix (..),
                                                                foldFix)
import           Data.Maybe                                    (isJust,
                                                                isNothing)
import           Data.Set                                      (Set)
import qualified Data.Set                                      as Set
import qualified Language.Cimple                               as C
import           Language.Hic.TypeSystem.Core.Base             (FlatType (..),
                                                                FullTemplateF (..),
                                                                Phase (..),
                                                                Qualifier (..),
                                                                StdType (..),
                                                                TemplateId (..),
                                                                TypeInfo,
                                                                TypeInfoF (..),
                                                                TypeRef (..),
                                                                fromFlat,
                                                                normalizeType,
                                                                pattern Array,
                                                                pattern BuiltinType,
                                                                pattern Conflict,
                                                                pattern Const,
                                                                pattern ExternalType,
                                                                pattern Function,
                                                                pattern IntLit,
                                                                pattern Nonnull,
                                                                pattern Nullable,
                                                                pattern Owner,
                                                                pattern Pointer,
                                                                pattern Proxy,
                                                                pattern Singleton,
                                                                pattern Sized,
                                                                pattern Template,
                                                                pattern TypeRef,
                                                                pattern Unconstrained,
                                                                pattern Var,
                                                                stripLexemes,
                                                                toFlat)
import qualified Language.Hic.TypeSystem.Core.Base             as TS
import qualified Language.Hic.TypeSystem.Core.Canonicalization as Canonicalization
import           Language.Hic.TypeSystem.Core.Lattice
import           Language.Hic.TypeSystem.Core.Qualification    (QualState (..))
import           Language.Hic.TypeSystem.Core.TypeGraph        (fromTypeInfo,
                                                                toTypeInfo)

spec :: Spec
spec = do
    let (~=~) t1 t2 = stripLexemes (normalizeType t1) == stripLexemes (normalizeType t2)
    let (====) t1 t2 = Canonicalization.bisimilar (normalizeType t1) (normalizeType t2)

    let shouldBeBisimilar a b =
            if Canonicalization.bisimilar (normalizeType a) (normalizeType b)
            then return ()
            else stripLexemes (normalizeType a) `shouldBe` stripLexemes (normalizeType b)

    let shouldBeSubtypeOf a b =
            if subtypeOf a b
            then return ()
            else expectationFailure $ "Expected\n  " ++ show (normalizeType a) ++ "\nto be a subtype of\n  " ++ show (normalizeType b)

    describe "subtypeOf" $ do
        it "is reflexive" $ property $ \t ->
            subtypeOf (t :: TypeInfo 'Local) t

        it "handles Singleton to BuiltinType" $ do
            subtypeOf (Singleton S32Ty 1) (BuiltinType S32Ty) `shouldBe` True

        it "handles Nonnull to base type" $ do
            let p = Pointer (BuiltinType S32Ty)
            subtypeOf (Nonnull p) p `shouldBe` True

        it "handles base type to Nullable" $ do
            let p = Pointer (BuiltinType S32Ty)
            subtypeOf p (Nullable p) `shouldBe` True

        it "handles base type to Const" $ do
            let p = Pointer (BuiltinType S32Ty)
            subtypeOf p (Const p) `shouldBe` True

        it "disallows base type to Nonnull" $ do
            let p = Pointer (BuiltinType S32Ty)
            subtypeOf p (Nonnull p) `shouldBe` False

        it "disallows Nullable to base type" $ do
            let p = Pointer (BuiltinType S32Ty)
            subtypeOf (Nullable p) p `shouldBe` False

        it "handles nullptr_t subtyping" $ do
            let p = Pointer (BuiltinType S32Ty)
            subtypeOf (BuiltinType NullPtrTy) p `shouldBe` True
            subtypeOf (BuiltinType NullPtrTy) (Nullable p) `shouldBe` True
            subtypeOf (BuiltinType NullPtrTy) (Nonnull p) `shouldBe` False

        it "handles integer subtyping (loose)" $ do
            subtypeOf (BuiltinType S16Ty) (BuiltinType S32Ty) `shouldBe` True
            subtypeOf (BuiltinType S32Ty) (BuiltinType S16Ty) `shouldBe` False

        it "handles structural subtyping for pointers" $ do
            let p1 = Pointer (Singleton S32Ty 1)
            let p2 = Pointer (BuiltinType S32Ty)
            -- Pointers are invariant in C.
            subtypeOf p1 p2 `shouldBe` False

        it "handles Var nodes by peeling them" $ do
            let l = C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdAnonymous 0 (Just "x"))
            let v = Var l (Singleton S32Ty 1)
            subtypeOf v (BuiltinType S32Ty) `shouldBe` True

        it "disallows unsound T** to const T** conversion (C rule)" $ do
            let t = BuiltinType S32Ty
            let tpp = Pointer (Pointer t)
            let ctpp = Pointer (Pointer (Const t))
            subtypeOf tpp ctpp `shouldBe` False

        it "allows sound T** to T* const* conversion (C rule)" $ do
            let t = BuiltinType S32Ty
            let tpp = Pointer (Pointer t)
            let tcp = Pointer (Const (Pointer t))
            subtypeOf tpp tcp `shouldBe` True

    describe "Lattice Bounds (Rigorous Solver)" $ do
        it "treats Pointer Unconstrained as bottom of pointers" $ do
            let p_bot = Pointer Unconstrained
            let p_int = Pointer (BuiltinType S32Ty)
            subtypeOf p_bot p_int `shouldBe` True
            join p_bot p_int ~=~ p_int `shouldBe` True
            meet p_bot p_int ~=~ p_bot `shouldBe` True

        it "treats Pointer Conflict as top of pointers" $ do
            let p_top = Pointer Conflict
            let p_int = Pointer (BuiltinType S32Ty)
            subtypeOf p_int p_top `shouldBe` True
            join p_int p_top ~=~ p_top `shouldBe` True
            meet p_int p_top ~=~ p_int `shouldBe` True

        it "treats Array Unconstrained as bottom of arrays" $ do
            let a_bot = Array (Just Unconstrained) []
            let a_int = Array (Just (BuiltinType S32Ty)) []
            subtypeOf a_bot a_int `shouldBe` True
            join a_bot a_int ~=~ a_int `shouldBe` True
            meet a_bot a_int ~=~ a_bot `shouldBe` True

    describe "join" $ do
        it "is reflexive" $ do
            join (BuiltinType S32Ty) (BuiltinType S32Ty) `shouldBe` (BuiltinType S32Ty)

        it "joins Arrays with same dimension" $ do
            let a1 = Array (Just (Singleton S32Ty 1)) [BuiltinType S32Ty]
            let a2 = Array (Just (Singleton S32Ty 2)) [BuiltinType S32Ty]
            -- Targets differ (1 vs 2), so it must force const.
            -- It stays an Array but with no dimensions (since dimensions match, but we don't know the values).
            join a1 a2 `shouldBe` (Array (Just (Const (BuiltinType S32Ty))) [BuiltinType S32Ty])

        it "joins Arrays with different dimensions to a Pointer" $ do
            let a1 = Array (Just (Singleton S32Ty 1)) [BuiltinType S32Ty]
            let a2 = Array (Just (Singleton S32Ty 2)) []
            -- Targets differ, must force const. Stays Array with no dimensions.
            join a1 a2 `shouldBe` (Array (Just (Const (BuiltinType S32Ty))) [])

        it "joins identical Arrays with different dimensions" $ do
            let a1 = Array (Just (BuiltinType S32Ty)) [BuiltinType S32Ty]
            let a2 = Array (Just (BuiltinType S32Ty)) []
            -- Targets match, so it can stay an Array but with no dimensions.
            join a1 a2 `shouldBe` (Array (Just (BuiltinType S32Ty)) [])

        it "joins Functions with same arity" $ do
            let f1 = Function (Singleton S32Ty 1) [BuiltinType S32Ty]
            let f2 = Function (Singleton S32Ty 2) [BuiltinType S32Ty]
            join f1 f2 `shouldBe` (Function (BuiltinType S32Ty) [BuiltinType S32Ty])

        it "joins Var nodes by peeling them" $ do
            let l = C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdAnonymous 0 (Just "x"))
            let v = Var l (Singleton S32Ty 1)
            join v (Singleton S32Ty 2) `shouldBe` (BuiltinType S32Ty)

        it "widens Singleton to BuiltinType on mismatch" $ do
            join (Singleton S32Ty 1) (Singleton S32Ty 2) `shouldBe` (BuiltinType S32Ty)

        it "preserves identical Singletons" $ do
            join (Singleton S32Ty 1) (Singleton S32Ty 1) `shouldBe` (Singleton S32Ty 1)

        it "widens Singleton and BuiltinType to BuiltinType" $ do
            join (Singleton S32Ty 1) (BuiltinType S32Ty) `shouldBe` (BuiltinType S32Ty)

        it "joins pointers by joining their target types" $ do
            join (Pointer (Singleton S32Ty 1)) (Pointer (Singleton S32Ty 2)) `shouldBe` (Pointer (Const (BuiltinType S32Ty)))

        it "joins Nonnull and base type to base type" $ do
            let p = Pointer (BuiltinType S32Ty)
            join (Nonnull p) p `shouldBe` p

        it "joins Nonnull and Nullable to Nullable" $ do
            let p = Pointer (BuiltinType S32Ty)
            join (Nonnull p) (Nullable p) `shouldBe` (Nullable p)

        it "joins function types contravariantly in parameters" $ do
            let f1 = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
            let f2 = Function (BuiltinType VoidTy) [Singleton S32Ty 2]
            -- join(f1, f2) = meet(param1, param2) -> join(ret1, ret2)
            -- meet(int, 2) = 2
            join f1 f2 `shouldBe` Function (BuiltinType VoidTy) [Singleton S32Ty 2]

        it "joins deeply nested qualified pointers" $ do
            let p1 = Pointer (Nonnull (Pointer (BuiltinType S32Ty)))
            let p2 = Pointer (Nullable (Pointer (BuiltinType S32Ty)))
            join p1 p2 `shouldBe` Pointer (Const (Nullable (Pointer (BuiltinType S32Ty))))

        it "is symmetric for complex joins" $ do
            let p = Pointer (BuiltinType S32Ty)
            join (Nonnull p) p `shouldBe` join p (Nonnull p)

    describe "meet" $ do
        it "is reflexive" $ do
            meet (BuiltinType S32Ty) (BuiltinType S32Ty) `shouldBe` (BuiltinType S32Ty)

        it "narrows Template to concrete type" $ do
            let t = TS.Template (TIdSolver 0 Nothing) Nothing
            let concrete = BuiltinType S32Ty
            -- Template is an incomparable atom, meet with concrete is Bottom.
            meet t concrete `shouldBe` Unconstrained
            meet concrete t `shouldBe` Unconstrained

        it "narrows BuiltinType to Singleton" $ do
            meet (BuiltinType S32Ty) (Singleton S32Ty 1) `shouldBe` (Singleton S32Ty 1)

        it "meets pointers by meeting their target types" $ do
            let p1 = Pointer (BuiltinType S32Ty)
            let p2 = Pointer (Singleton S32Ty 1)
            -- Pointers are invariant, and neither is Const, so they are incomparable.
            -- Their GLB is Pointer bot.
            meet p1 p2 `shouldBe` Pointer Unconstrained

        it "meets pointers by meeting their target types (Const)" $ do
            let p1 = Pointer (Const (BuiltinType S32Ty))
            let p2 = Pointer (Singleton S32Ty 1)
            -- p2 <: p1 because p1's target is Const.
            subtypeOf p2 p1 `shouldBe` True
            meet p1 p2 `shouldBe` p2

        it "meets Nonnull and base type to Nonnull" $ do
            let p = Pointer (BuiltinType S32Ty)
            meet (Nonnull p) p `shouldBe` Nonnull p
            meet p (Nonnull p) `shouldBe` Nonnull p

        it "meets Const and base type to base type" $ do
            let p = Pointer (BuiltinType S32Ty)
            meet (Const p) p `shouldBe` p
            meet p (Const p) `shouldBe` p

        it "meets pointers by meeting their target types (Const) (repro)" $ do
            let p1 = Pointer (Const (BuiltinType S32Ty))
            let p2 = Pointer (Singleton S32Ty 1)
            -- p2 <: p1 because p1's target is Const.
            subtypeOf p2 p1 `shouldBe` True
            meet p1 p2 `shouldBe` p2

    describe "repro" $ do
        it "join is an upper bound (repro)" $ do
            let t1 = Function (Array (Just (BuiltinType U08Ty)) [Singleton U08Ty 3]) []
            let t2 = Function (Array (Just (BuiltinType U08Ty)) [Singleton U08Ty 4]) []
            let j = join t1 t2
            subtypeOf t1 j `shouldBe` True
            subtypeOf t2 j `shouldBe` True

        it "join is an upper bound (repro 2)" $ do
            let t1 = Pointer (BuiltinType VoidTy)
            let t2 = Pointer (BuiltinType S32Ty)
            let j = join t1 t2
            subtypeOf t1 j `shouldBe` True
            subtypeOf t2 j `shouldBe` True

        it "join is an upper bound (repro 3)" $ do
            let t1 = Pointer (Pointer (BuiltinType S32Ty))
            let t2 = Pointer (BuiltinType S32Ty)
            let j = join t1 t2
            subtypeOf t1 j `shouldBe` True
            subtypeOf t2 j `shouldBe` True

        it "join vs subtypeOf (repro 4)" $ do
            let a = Nonnull (Pointer (BuiltinType S32Ty))
            let b = Pointer (BuiltinType S32Ty)
            subtypeOf a b `shouldBe` True
            join a b ~=~ b `shouldBe` True

        it "meet is associative (repro 5)" $ do
            let t1 = BuiltinType NullPtrTy
            let t2 = Pointer Unconstrained
            let t3 = Pointer (BuiltinType S32Ty)
            meet t1 (meet t2 t3) ~=~ meet (meet t1 t2) t3 `shouldBe` True

        it "satisfies absorption (repro 6)" $ do
            pendingWith "Currently failing"
            let loc = C.L (C.AlexPn (-31) (-41) (-36)) C.CmtWord (TIdRec 37)
            let t1 = Sized (Array Nothing []) loc
            let t2 = Array Nothing [Singleton NullPtrTy (-16)]
            let m = meet t1 t2
            let j = join t1 m
            Canonicalization.bisimilar (normalizeType j) (normalizeType t1) `shouldBe` True

        it "satisfies absorption (repro 7)" $ do
            pendingWith "Hypothesis: Lattice absorption is violated because join/meet with Const and Pointer/Array structures don't commute as expected due to the rigid transition's strict invariance rules."
            let t1 = Array (Just (Pointer (Singleton F64Ty 6))) []
            let t2 = Array (Just (Const (Pointer (BuiltinType U32Ty)))) []
            let m = meet t1 t2
            let j = join t1 m
            Canonicalization.bisimilar (normalizeType j) (normalizeType t1) `shouldBe` True

        it "meet is a lower bound (repro 9)" $ do
            let t1 = Pointer (BuiltinType S64Ty)
            let t2 = Array (Just (Const (BuiltinType U32Ty))) []
            let m = meet t1 t2
            m `shouldBeSubtypeOf` t1
            m `shouldBeSubtypeOf` t2

        it "absorption join/meet (repro 10)" $ do
            pendingWith "Hypothesis: join/meet with Array and Pointer to Nonnull/Const types fails absorption because normalized forms differ in unexpected qualifiers."
            let t1 = Array (Just (BuiltinType CharTy)) []
            let t2 = Pointer (Nonnull (Const (BuiltinType S16Ty)))
            let m = meet t1 t2
            join t1 m `shouldBeBisimilar` t1

        it "join vs subtypeOf (repro 11)" $ do
            pendingWith "Currently failing"
            let loc = C.L (C.AlexPn 17 0 27) C.LitFloat (TIdPoly 29 (-14) (Just "A\1088300\178807~v\994159\ar") TS.TopLevel)
            let t1 = Pointer (Sized TS.VarArg loc)
            let t2 = Pointer TS.VarArg
            t1 `shouldBeSubtypeOf` t2
            join t1 t2 `shouldBeBisimilar` t2

        it "sized recursive function is not a subtype of unsized (repro 8)" $ do
            pendingWith "Currently failing"
            let t1 = Function TS.VarArg [Template (TIdRec 0) Nothing]
            let loc = C.L (C.AlexPn 1 (-2) (-2)) C.PctPipePipe (TIdRec 0)
            let a = Sized t1 loc
            let c = t1
            -- a = Sized (Function a) loc
            -- c = Function c
            -- a <: c iff Function a <: Function c iff c <: a
            -- c <: a is False because c is Unsized and a is Sized.
            subtypeOf a c `shouldBe` False

            -- The GLB should be an alternating structure:
            -- m = Sized (Function (Function m)) loc
            let m = meet a c
            let expected_m = Sized (Function TS.VarArg [Function TS.VarArg [Template (TIdRec 1) Nothing]]) loc
            Canonicalization.bisimilar (TS.normalizeType m) (TS.normalizeType expected_m) `shouldBe` True

    describe "properties" $ do
        prop "join is reflexive" $ \t ->
            join (t :: TypeInfo 'Local) t ==== t

        prop "join is symmetric" $ \t1 t2 ->
            join (t1 :: TypeInfo 'Local) t2 ==== join t2 t1

        prop "join is an upper bound" $ \t1 t2 ->
            let j = join (t1 :: TypeInfo 'Local) t2
            in subtypeOf t1 j && subtypeOf t2 j

        prop "meet is reflexive" $ \t ->
            meet (t :: TypeInfo 'Local) t ==== t

        prop "meet is symmetric" $ \t1 t2 ->
            meet (t1 :: TypeInfo 'Local) t2 ==== meet (t2 :: TypeInfo 'Local) t1

        prop "meet is a lower bound" $ \t1 t2 ->
            let m = meet (t1 :: TypeInfo 'Local) t2
            in subtypeOf m t1 && subtypeOf m t2

        it "join is associative" $ property $ \t1 t2 t3 -> do
            pendingWith "Hypothesis: join is not associative for Function types when VarArg is involved, likely due to how getTargetState handles terminal nodes (VarArg) during product construction."
            let j1 = join (t1 :: TypeInfo 'Local) (join t2 t3)
                j2 = join (join t1 t2) t3
            j1 `shouldBeBisimilar` j2

        it "meet is associative" $ do
            pendingWith "Currently failing"
            _ <- return $ property $ \t1 t2 t3 ->
                let m1 = meet (t1 :: TypeInfo 'Local) (meet t2 t3)
                    m2 = meet (meet t1 t2) t3
                in m1 ==== m2
            pure ()

        it "absorption join/meet" $ do
            pendingWith "Currently failing"
            _ <- return $ property $ \(t1 :: TypeInfo 'Local) t2 ->
                Canonicalization.bisimilar (TS.normalizeType (join t1 (meet t1 t2))) (TS.normalizeType t1)
            pure ()

        it "absorption meet/join" $ do
            pendingWith "Currently failing"
            _ <- return $ property $ \(t1 :: TypeInfo 'Local) t2 ->
                Canonicalization.bisimilar (TS.normalizeType (meet t1 (join t1 t2))) (TS.normalizeType t1)
            pure ()

        it "subtypeOf is transitive" $ do
            pendingWith "Currently failing"
            _ <- return $ property $ \(b :: TypeInfo 'Local) ->
                forAll (genSubtype b) $ \a ->
                    forAll (genSupertype b) $ \c ->
                        subtypeOf (a :: TypeInfo 'Local) (c :: TypeInfo 'Local)
            pure ()

--      prop "join vs subtypeOf" $ \t1 t2 ->
--          let (a, b) = (t1 :: TypeInfo 'Local, t2 :: TypeInfo 'Local)
--          in (join a b ==== b) == subtypeOf a b

        prop "meet vs subtypeOf" $ \t1 t2 ->
            let (a, b) = (t1 :: TypeInfo 'Local, t2 :: TypeInfo 'Local)
            in (meet a b ==== a) == subtypeOf a b

        it "join is monotonic" $ do
            pendingWith "Currently failing"
            _ <- return $ property $ \(a :: TypeInfo 'Local) (c :: TypeInfo 'Local) ->
                forAll (genSupertype a) $ \b ->
                    subtypeOf (join a c) (join (b :: TypeInfo 'Local) c)
            pure ()

--      it "meet is monotonic" $
--          property $ \(b :: TypeInfo 'Local) (c :: TypeInfo 'Local) ->
--              forAll (genSubtype b) $ \a ->
--                  subtypeOf (meet (a :: TypeInfo 'Local) c) (meet b c)

    describe "Graph-based operations (Rigorous Solver)" $ do
        it "joinGraph(Nonnull P, P) == P" $ do
            let p = Pointer (BuiltinType S32Ty)
            let nnp = Nonnull p
            let g1 = fromTypeInfo nnp
            let g2 = fromTypeInfo p
            let res = joinGraph (const False) g1 g2
            toTypeInfo res `shouldBe` p

        it "joinGraph(P, Nonnull P) == P" $ do
            let p = Pointer (BuiltinType S32Ty)
            let nnp = Nonnull p
            let g1 = fromTypeInfo p
            let g2 = fromTypeInfo nnp
            let res = joinGraph (const False) g1 g2
            toTypeInfo res `shouldBe` p

        it "meetGraph(Nonnull P, P) == Nonnull P" $ do
            let p = Pointer (BuiltinType S32Ty)
            let nnp = Nonnull p
            let g1 = fromTypeInfo nnp
            let g2 = fromTypeInfo p
            let res = meetGraph (const False) g1 g2
            toTypeInfo res `shouldBe` nnp

        it "meetGraph(P, Nonnull P) == Nonnull P" $ do
            let p = Pointer (BuiltinType S32Ty)
            let nnp = Nonnull p
            let g1 = fromTypeInfo p
            let g2 = fromTypeInfo nnp
            let res = meetGraph (const False) g1 g2
            toTypeInfo res `shouldBe` nnp

        it "joinGraph is consistent with join" $ property $ \(t1 :: TypeInfo 'Local) (t2 :: TypeInfo 'Local) ->
            let g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
                gj = joinGraph (const False) g1 g2
                tj = join t1 t2
            in stripLexemes (toTypeInfo gj) `shouldBe` stripLexemes tj

        it "meetGraph is consistent with meet" $ property $ \(t1 :: TypeInfo 'Local) (t2 :: TypeInfo 'Local) ->
            let g1 = fromTypeInfo t1
                g2 = fromTypeInfo t2
                gm = meetGraph (const False) g1 g2
                tm = meet t1 t2
            in stripLexemes (toTypeInfo gm) `shouldBe` stripLexemes tm

-- | Checks if a type contains a recursion point.
hasRecursion :: TypeInfo p -> Bool
hasRecursion = foldFix $ \case
    TemplateF (FT (TIdRec _) _) -> True
    f                           -> any id f

-- | Generates a type that is guaranteed to be a subtype of the given type.
genSubtype :: TS.ArbitraryTemplateId p => TypeInfo p -> Gen (TypeInfo p)
genSubtype t
    | hasRecursion t = oneof [return t, return Unconstrained]
    | otherwise = oneof
    [ return t
    , return Unconstrained
    , let f = toFlat t in if isNothing (ftSize f) && not (isFunction $ ftStructure f) then do sz <- arbitrary; return (Sized t sz) else return t
    , let f = toFlat t
      in do
          qs' <- genSubQuals (ftQuals f)
          s'  <- genSubStruct (ftStructure f)
          return $ fromFlat (FlatType s' qs' (ftSize f))
    ]
  where
    isFunction (TS.FunctionF _ _) = True
    isFunction _                  = False
    genSubQuals qs = do
        let canRemoveNullable = Set.member QNullable qs
        let canAddNonnull = not (Set.member QNonnull qs) && not (Set.member QNullable qs)
        let canRemoveConst = Set.member QConst qs
        let canRemoveOwner = Set.member QOwner qs
        actions <- elements $ filter fst
            [ (True, return qs)
            , (canRemoveNullable, return $ Set.delete QNullable qs)
            , (canAddNonnull, return $ Set.insert QNonnull qs)
            , (canRemoveConst, return $ Set.delete QConst qs)
            , (canRemoveOwner, return $ Set.delete QOwner qs)
            ]
        snd actions

    genSubStruct = \case
        TS.BuiltinTypeF b | TS.isInt b -> TS.BuiltinTypeF <$> genSubInt b
        TS.BuiltinTypeF b -> oneof [return (TS.BuiltinTypeF b), return (TS.SingletonF b 0)]
        TS.PointerF inner ->
            let fInner = toFlat inner
                isConstInner = Set.member QConst (ftQuals fInner)
            in if isConstInner
               then TS.PointerF <$> genSubtype inner
               else return $ TS.PointerF inner
        TS.ArrayF (Just inner) ds ->
            let fInner = toFlat inner
                isConstInner = Set.member QConst (ftQuals fInner)
            in if isConstInner
               then TS.ArrayF . Just <$> genSubtype inner <*> pure ds
               else return $ TS.ArrayF (Just inner) ds
        s -> return s

    allInts = [VoidTy, BoolTy, CharTy, U08Ty, S08Ty, U16Ty, S16Ty, U32Ty, S32Ty, U64Ty, S64Ty, SizeTy, F32Ty, F64Ty, NullPtrTy]
    genSubInt b = elements [ b' | b' <- allInts, TS.isInt b', b' <= b ]

-- | Generates a type that is guaranteed to be a supertype of the given type.
genSupertype :: TS.ArbitraryTemplateId p => TypeInfo p -> Gen (TypeInfo p)
genSupertype t
    | hasRecursion t = oneof [return t, return Conflict]
    | otherwise = oneof
    [ return t
    , return Conflict
    , let f = toFlat t in if isJust (ftSize f) then return (fromFlat (f { ftSize = Nothing })) else return t
    , let f = toFlat t
      in do
          qs' <- genSuperQuals (ftQuals f)
          s'  <- genSuperStruct (ftStructure f)
          return $ fromFlat (FlatType s' qs' (ftSize f))
    ]
  where
    genSuperQuals qs = do
        let canAddNullable = not (Set.member QNullable qs) && not (Set.member QNonnull qs)
        let canRemoveNonnull = Set.member QNonnull qs
        let canAddConst = not (Set.member QConst qs)
        let canAddOwner = not (Set.member QOwner qs)
        actions <- elements $ filter fst
            [ (True, return qs)
            , (canAddNullable, return $ Set.insert QNullable qs)
            , (canRemoveNonnull, return $ Set.delete QNonnull qs)
            , (canAddConst, return $ Set.insert QConst qs)
            , (canAddOwner, return $ Set.insert QOwner qs)
            ]
        snd actions

    genSuperStruct = \case
        TS.SingletonF b _ -> return $ TS.BuiltinTypeF b
        TS.BuiltinTypeF b | TS.isInt b -> TS.BuiltinTypeF <$> genSuperInt b
        TS.ArrayF (Just inner) ds -> oneof
            [ return $ TS.PointerF (TS.Const inner)
            , do s <- genSupertype inner
                 let fS = toFlat s
                 if Set.member QConst (ftQuals fS)
                     then return $ TS.ArrayF (Just s) ds
                     else return $ TS.ArrayF (Just (TS.Const s)) ds
            , return $ TS.ArrayF (Just inner) [] -- Incomplete array is supertype
            ]
        TS.PointerF inner ->
            let fInner = toFlat inner
                isConstInner = Set.member QConst (ftQuals fInner)
            in if isConstInner
               then do
                   s <- genSupertype inner
                   let fS = toFlat s
                   if Set.member QConst (ftQuals fS)
                       then return $ TS.PointerF s
                       else return $ TS.PointerF (TS.Const s)
               else return $ TS.PointerF inner
        s -> return s

    allInts = [VoidTy, BoolTy, CharTy, U08Ty, S08Ty, U16Ty, S16Ty, U32Ty, S32Ty, U64Ty, S64Ty, SizeTy, F32Ty, F64Ty, NullPtrTy]
    genSuperInt b = elements [ b' | b' <- allInts, TS.isInt b', b' >= b ]
