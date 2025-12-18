{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Core.Transition.Types
    ( Polarity (..)
    , ProductState (..)
    , RigidNodeF (..)
    , ValueStructure (..)
    , SpecialNode (..)
    ) where

import           GHC.Generics                               (Generic)
import           Language.Cimple                            (Lexeme (..))
import           Language.Hic.Core.TypeSystem               (FullTemplateF (..),
                                                             StdType (..),
                                                             TypeRef (..))
import           Language.Hic.TypeSystem.Core.Qualification (Constness (..),
                                                             Nullability (..),
                                                             Ownership (..),
                                                             QualState (..))
import           Test.QuickCheck                            (Arbitrary (..),
                                                             arbitraryBoundedEnum,
                                                             genericShrink,
                                                             oneof)

-- | Polarity of the lattice operation (Join/Upper Bound or Meet/Lower Bound).
data Polarity = PJoin | PMeet deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance Arbitrary Polarity where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

-- | The state of the product automaton.
data ProductState = ProductState
    { psPolarity   :: Polarity
    , psQualL      :: QualState
    , psQualR      :: QualState
    , psForceConst :: Bool
    } deriving (Show, Eq, Ord, Generic)

-- | A canonicalized type node with attributes.
-- Enforces correct-by-construction property: attributes only where valid.
data RigidNodeF tid a
    = RFunction a [a] Constness (Maybe (Lexeme tid))
    | RValue (ValueStructure tid a) Constness (Maybe (Lexeme tid))
    | RSpecial SpecialNode
    deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

data ValueStructure tid a
    = VBuiltin StdType
    | VPointer a Nullability Ownership
    | VTemplate (FullTemplateF tid a) Nullability Ownership
    | VTypeRef TypeRef (Lexeme tid) [a]
    | VArray (Maybe a) [a]
    | VSingleton StdType Integer
    | VExternal (Lexeme tid)
    | VIntLit (Lexeme tid)
    | VNameLit (Lexeme tid)
    | VEnumMem (Lexeme tid)
    | VVarArg
    deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

data SpecialNode = SUnconstrained | SConflict
    deriving (Show, Eq, Ord, Generic, Bounded, Enum)

instance Arbitrary ProductState where
    arbitrary = ProductState <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    shrink = genericShrink

instance Arbitrary SpecialNode where
    arbitrary = arbitraryBoundedEnum
    shrink = genericShrink

instance (Arbitrary tid, Arbitrary a) => Arbitrary (RigidNodeF tid a) where
    arbitrary = oneof
        [ RFunction <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        , RValue <$> arbitrary <*> arbitrary <*> arbitrary
        , RSpecial <$> arbitrary
        ]
    shrink = genericShrink

instance (Arbitrary tid, Arbitrary a) => Arbitrary (ValueStructure tid a) where
    arbitrary = oneof
        [ VBuiltin <$> arbitrary
        , VPointer <$> arbitrary <*> arbitrary <*> arbitrary
        , VTemplate <$> arbitrary <*> arbitrary <*> arbitrary
        , VTypeRef <$> arbitrary <*> arbitrary <*> arbitrary
        , VArray <$> arbitrary <*> arbitrary
        , VSingleton <$> arbitrary <*> arbitrary
        , VExternal <$> arbitrary
        , VIntLit <$> arbitrary
        , VNameLit <$> arbitrary
        , VEnumMem <$> arbitrary
        ]
    shrink = genericShrink
