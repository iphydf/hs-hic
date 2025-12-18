{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Core.Constraints
    ( Constraint (..)
    , collectTemplates
    , mapTypes
    ) where

import           Data.Aeson                   (ToJSON)
import           Data.List                    (nub)
import           Data.Text                    (Text)
import qualified Data.Text                    as T
import           GHC.Generics                 (Generic)
import           Language.Cimple              (Lexeme (..))
import           Language.Hic.Core.Errors     (Context (..),
                                               MismatchReason (..))
import           Language.Hic.Core.TypeSystem (ArbitraryTemplateId (..),
                                               FullTemplate, Phase (..),
                                               TypeInfo,
                                               collectUniqueTemplateVars)
import           Test.QuickCheck              (Arbitrary (..), oneof, scale)

-- | A type constraint represents a relationship that must hold between types.
-- It is the core language used by the solver to perform type inference and
-- check for soundness.
data Constraint (p :: Phase)
    = Equality (TypeInfo p) (TypeInfo p) (Maybe (Lexeme Text)) [Context p] MismatchReason
    -- ^ T1 and T2 must be the same type.
    | Subtype (TypeInfo p) (TypeInfo p) (Maybe (Lexeme Text)) [Context p] MismatchReason
    -- ^ The first type (actual) must be a subtype of the second (expected).
    | Lub (TypeInfo p) [TypeInfo p] (Maybe (Lexeme Text)) [Context p] MismatchReason
    -- ^ The first type is the Least Upper Bound (LUB) of the given list of types.
    | Callable (TypeInfo p) [TypeInfo p] (TypeInfo p) (Maybe (Lexeme Text)) [Context p] (Maybe Integer) Bool
    -- ^ Represents a function call. Params: FunctionType, ArgTypes, ReturnType, Location, Context, CallSiteId, ShouldRefresh.
    | HasMember (TypeInfo p) Text (TypeInfo p) (Maybe (Lexeme Text)) [Context p] MismatchReason
    -- ^ Represents a struct/union member access. Params: BaseType, MemberName, ResultType, Location, Context, Reason.
    | CoordinatedPair (TypeInfo p) (TypeInfo p) (TypeInfo p) (Maybe (Lexeme Text)) [Context p] (Maybe Integer)
    -- ^ Conditional constraint: If the first type (trigger) is Nonnull,
    -- then the second (actual) must be a subtype of the third (expected).
    deriving (Show, Eq, Ord, Generic)

instance ArbitraryTemplateId p => Arbitrary (Constraint p) where
    arbitrary = oneof
        [ Equality <$> arbitrary <*> arbitrary <*> return Nothing <*> arbitrary <*> arbitrary
        , Subtype <$> arbitrary <*> arbitrary <*> return Nothing <*> arbitrary <*> arbitrary
        , Lub <$> arbitrary <*> arbitrary <*> return Nothing <*> arbitrary <*> arbitrary
        , Callable <$> arbitrary <*> arbitrary <*> arbitrary <*> return Nothing <*> arbitrary <*> arbitrary <*> arbitrary
        , HasMember <$> arbitrary <*> (scale (const 2) $ arbitrary >>= return . T.pack) <*> arbitrary <*> return Nothing <*> arbitrary <*> arbitrary
        , CoordinatedPair <$> arbitrary <*> arbitrary <*> arbitrary <*> return Nothing <*> arbitrary <*> arbitrary
        ]

instance ToJSON (Constraint p)

-- | Collects all unique templates used across all types in the constraint.
collectTemplates :: Constraint p -> [FullTemplate p]
collectTemplates = nub . collectUniqueTemplateVars . \case
    Equality t1 t2 _ _ _         -> [t1, t2]
    Subtype t1 t2 _ _ _          -> [t1, t2]
    Lub t1 ts _ _ _              -> t1 : ts
    Callable t1 ts t2 _ _ _ _    -> t1 : t2 : ts
    HasMember t1 _ t2 _ _ _      -> [t1, t2]
    CoordinatedPair t1 t2 t3 _ _ _ -> [t1, t2, t3]

-- | Applies a transformation function to all TypeInfo nodes within the constraint.
mapTypes :: (TypeInfo p -> TypeInfo p) -> Constraint p -> Constraint p
mapTypes f = \case
    Equality t1 t2 ml ctx r         -> Equality (f t1) (f t2) ml ctx r
    Subtype t1 t2 ml ctx r          -> Subtype (f t1) (f t2) ml ctx r
    Lub t1 ts ml ctx r              -> Lub (f t1) (map f ts) ml ctx r
    Callable t1 ts t2 ml ctx i s    -> Callable (f t1) (map f ts) (f t2) ml ctx i s
    HasMember t1 n t2 ml ctx r      -> HasMember (f t1) n (f t2) ml ctx r
    CoordinatedPair t1 t2 t3 ml ctx i -> CoordinatedPair (f t1) (f t2) (f t3) ml ctx i
