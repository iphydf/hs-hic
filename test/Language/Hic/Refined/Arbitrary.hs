{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Hic.Refined.Arbitrary where

import           Data.Bits                        (shiftL, (.&.), (.|.))
import           Data.Foldable                    (foldlM)
import           Data.IntMap.Strict               (IntMap)
import qualified Data.IntMap.Strict               as IntMap
import           Data.List                        (foldl')
import qualified Data.List                        as List
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.Text                        (Text)
import qualified Data.Text                        as T
import           Data.Word                        (Word32, Word64)
import           Language.Cimple                  (AlexPosn (..), Lexeme (..),
                                                   LexemeClass (..))
import           Language.Hic.Refined.Context
import           Language.Hic.Refined.LatticeOp
import           Language.Hic.Refined.PathContext
import           Language.Hic.Refined.Solver
import           Language.Hic.Refined.State
import           Language.Hic.Refined.Types
import           Test.QuickCheck                  (Arbitrary (..), Gen,
                                                   arbitraryBoundedEnum, choose,
                                                   elements, listOf, listOf1,
                                                   oneof, resize, scale, sized,
                                                   vectorOf)

instance Arbitrary StdType where
    arbitrary = arbitraryBoundedEnum

instance Arbitrary Quals where
    arbitrary = do
        p <- arbitrary
        c <- if p then pure True else arbitrary
        return $ Quals c p

instance Arbitrary Nullability where
    arbitrary = arbitraryBoundedEnum

instance Arbitrary Ownership where
    arbitrary = arbitraryBoundedEnum

instance Arbitrary Polarity where
    arbitrary = arbitraryBoundedEnum

instance Arbitrary Variance where
    arbitrary = arbitraryBoundedEnum

instance Arbitrary LatticePhase where
    arbitrary = arbitraryBoundedEnum

instance Arbitrary TemplateId where
    arbitrary = oneof $
        [ TIdName . T.pack <$> listOf1 (elements ['a'..'z'])
        , TIdParam <$> arbitrary <*> arbitrary <*> pure Nothing
        , TIdSkolem <$> arbitrary <*> arbitrary <*> arbitrary
        , TIdInstance <$> arbitrary
        , TIdDeBruijn <$> choose (0, 30)
        ] ++
        -- Stable 'Nuisance' Names often encountered in Inference
        [ pure (TIdName "LIT_0")
        , pure (TIdName "T")
        , pure (TIdName "U")
        , TIdSkolem <$> elements [10, 20, 100] <*> elements [10, 20, 100] <*> choose (0, 5)
        ]

instance Arbitrary MappingContext where
    arbitrary = do
        count <- choose (0, 30)
        let n1 = min 14 count
        w1Data <- foldl' (\acc i -> (acc `shiftL` 4) .|. (i .&. 0xF)) 0 <$> vectorOf n1 (choose (0 :: Word64, 15))
        let w1 = (w1Data `shiftL` 8) .|. fromIntegral count

        let n2 = if count > 14 then count - 14 else 0
        w2 <- foldl' (\acc i -> (acc `shiftL` 4) .|. (i .&. 0xF)) 0 <$> vectorOf n2 (choose (0 :: Word64, 15))
        return $ MappingContext w1 w2

instance Arbitrary MappingRefinements where
    arbitrary = do
        count <- choose (0, 8)
        keys <- vectorOf count (arbitrary :: Gen Int)
        foldlM (\r k -> do
            nodeID <- arbitrary
            return $ setRefinement k nodeID r) emptyRefinements keys

instance Arbitrary ProductState where
    arbitrary = ProductState <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> choose (0, 30) <*> choose (0, 30) <*> oneof [pure Nothing, Just <$> ((,) <$> choose (0, 30) <*> arbitrary)] <*> pure Nothing <*> pure Nothing

instance Arbitrary PathRoot where
    arbitrary = oneof
        [ VarRoot <$> arbitrary
        , ParamRoot <$> arbitrary
        , InstanceRoot <$> arbitrary
        ]

instance Arbitrary PathStep where
    arbitrary = oneof
        [ FieldStep <$> arbitrary
        , IndexStep <$> arbitrary
        , VarStep <$> arbitrary
        ]

instance Arbitrary SymbolicPath where
    arbitrary = SymbolicPath <$> arbitrary <*> arbitrary

instance Arbitrary ValueConstraint where
    arbitrary = oneof [EqConst <$> arbitrary, NotConst <$> arbitrary, EqVariant <$> arbitrary]

instance Arbitrary PathContext where
    arbitrary = PathContext <$> arbitrary <*> arbitrary

instance Arbitrary T.Text where
    arbitrary = T.pack <$> listOf1 (elements ['a'..'z'])

instance (Arbitrary a, Ord a) => Arbitrary (AnyRigidNodeF TemplateId a) where
    arbitrary = oneof
        [ AnyRigidNodeF <$> (RObject <$> arbitrary <*> arbitrary)
        , AnyRigidNodeF <$> (RReference <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary)
        , AnyRigidNodeF <$> (RFunction <$> arbitrary <*> arbitrary)
        , AnyRigidNodeF <$> (RTerminal <$> arbitrary)
        ]

instance (Arbitrary a, Ord a) => Arbitrary (ObjectStructure TemplateId a) where
    arbitrary = sized $ \n ->
        let sub = resize (n `div` 2) arbitrary
            listLimit = scale (`div` 4)
        in oneof $
            [ VBuiltin <$> arbitrary
            , VSingleton <$> arbitrary <*> arbitrary
            , VNominal . dummyL . TIdName . T.pack <$> listOf1 (elements ['A'..'Z']) <*> listLimit (listOf sub)
            , VEnum . dummyL . TIdName . T.pack <$> listOf1 (elements ['A'..'Z'])
            , VVar <$> arbitrary <*> oneof [pure Nothing, Just <$> (IVar <$> arbitrary)]
            , VVariant . IntMap.fromList <$> listLimit (listOf ((,) <$> arbitrary <*> sub))
            , VProperty <$> sub <*> arbitrary
            , do terms <- Map.fromListWith (+) <$> listLimit (listOf1 ((,) <$> sub <*> choose (1, 10)))
                 return $ VSizeExpr (Map.toList terms)
            ] ++
            [ do count <- choose (1, 3)
                 body <- sub
                 return $ VExistential (map TIdDeBruijn [0..count-1]) body
            | n > 0 ] ++
            [ do body <- resize (n - 1) arbitrary
                 return $ VExistential [TIdDeBruijn 0] body
            | n > 2 ]

instance Arbitrary a => Arbitrary (RefStructure TemplateId a) where
    arbitrary = sized $ \n ->
        let sub = resize (n `div` 2) arbitrary
            listLimit = scale (`div` 4)
        in oneof
            [ Arr <$> sub <*> listLimit (listOf sub)
            , Ptr <$> arbitrary
            ]

instance Arbitrary a => Arbitrary (PtrTarget TemplateId a) where
    arbitrary = sized $ \n ->
        let sub = resize (n `div` 2) arbitrary
            listLimit = scale (`div` 4)
        in oneof
            [ TargetObject <$> sub
            , TargetFunction <$> listLimit (listOf sub) <*> arbitrary
            , TargetOpaque <$> arbitrary
            ]

instance Arbitrary a => Arbitrary (ReturnType a) where
    arbitrary = oneof [RetVal <$> arbitrary, pure RetVoid]

instance Arbitrary a => Arbitrary (TerminalNode a) where
    arbitrary = oneof [pure SBottom, pure SAny, pure SConflict]

instance Arbitrary PropertyKind where
    arbitrary = oneof
        [ pure PSize
        , pure PAlign
        , POffset . T.pack <$> listOf1 (elements ['a'..'z'])
        ]

instance Arbitrary a => Arbitrary (Index a) where
    arbitrary = oneof [ILit <$> arbitrary, IVar <$> arbitrary]

instance Arbitrary StructureKind where
    arbitrary = arbitraryBoundedEnum

instance Arbitrary Constraint where
    arbitrary = oneof
        [ do l <- choose (0, 20)
             r <- choose (0, 20)
             pol <- arbitrary
             ctx <- arbitrary
             path <- arbitrary
             dL <- choose (0, 30)
             dR <- choose (0, 30)
             return $ CSubtype l r pol ctx path dL dR Nothing ""
        , do l <- choose (0, 20)
             r <- choose (0, 20)
             return $ CInherit l r Nothing ""
        ]

-- | Helper for dummy Lexemes in tests.
dummyL :: t -> Lexeme t
dummyL = L (AlexPn 0 0 0) IdSueType
