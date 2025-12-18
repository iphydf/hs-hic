{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
module Language.Hic.Core.Errors
    ( Context(..)
    , MismatchReason(..)
    , Qualifier(..)
    , MismatchContext(..)
    , MismatchDetail(..)
    , Provenance(..)
    , TypeError(..)
    , ErrorInfo(..)
    ) where

import           Data.Aeson                    (ToJSON (..), object, (.=))
import           Data.Text                     (Text)
import qualified Data.Text                     as T
import           GHC.Generics                  (Generic)
import           Language.Cimple               (Lexeme (..), Node)
import           Language.Hic.Core.TypeSystem  (ArbitraryTemplateId (..),
                                                Phase (..), Qualifier (..),
                                                TypeInfo)
import           Prettyprinter                 (Doc, defaultLayoutOptions,
                                                layoutPretty, unAnnotate)
import           Prettyprinter.Render.Terminal (AnsiStyle)
import qualified Prettyprinter.Render.Text     as TR
import           Test.QuickCheck               (Arbitrary (..), oneof, scale)

-- | Context in which type checking is occurring
data Context (p :: Phase)
    = InFile FilePath
    | InFunction Text
    | InMacro Text
    | InMemberAccess Text
    | InExpr (Node (Lexeme Text))
    | InStmt (Node (Lexeme Text))
    | InInitializer (Node (Lexeme Text))
    | InUnification (TypeInfo p) (TypeInfo p) MismatchReason
    deriving (Show, Eq, Ord, Generic)

instance ArbitraryTemplateId p => Arbitrary (Context p) where
    arbitrary = oneof
        [ InFile <$> arbitrary
        , InFunction . T.pack <$> arbitrary
        , InMacro . T.pack <$> arbitrary
        , InMemberAccess . T.pack <$> arbitrary
        , InUnification <$> scale (\x -> x - 1) arbitrary <*> scale (\x -> x - 1) arbitrary <*> arbitrary
        ]

instance ToJSON (Context p)

-- | Reason for a type mismatch
data MismatchReason
    = GeneralMismatch
    | ReturnMismatch
    | ArgumentMismatch Int -- Index
    | AssignmentMismatch
    | InitializerMismatch
    deriving (Show, Eq, Ord, Generic)

instance Arbitrary MismatchReason where
    arbitrary = oneof
        [ return GeneralMismatch
        , return ReturnMismatch
        , ArgumentMismatch <$> arbitrary
        , return AssignmentMismatch
        , return InitializerMismatch
        ]

instance ToJSON MismatchReason

data MismatchContext
    = InPointer
    | InArray
    | InFunctionReturn
    | InFunctionParam Int
    deriving (Show, Eq, Ord, Generic)

instance Arbitrary MismatchContext where
    arbitrary = oneof
        [ return InPointer
        , return InArray
        , return InFunctionReturn
        , InFunctionParam <$> arbitrary
        ]

instance ToJSON MismatchContext

data MismatchDetail (p :: Phase)
    = MismatchDetail
        { mismatchExpected :: TypeInfo p
        , mismatchActual   :: TypeInfo p
        , mismatchReason   :: MismatchReason
        , mismatchInner    :: Maybe (MismatchContext, MismatchDetail p)
        }
    | MissingQualifier Qualifier (TypeInfo p) (TypeInfo p)
    | UnexpectedQualifier Qualifier (TypeInfo p) (TypeInfo p)
    | BaseMismatch (TypeInfo p) (TypeInfo p)
    | ArityMismatch Int Int -- Expected, Actual
    deriving (Show, Eq, Ord, Generic)

instance ToJSON (MismatchDetail p)

-- | Origin of a type or binding
data Provenance (p :: Phase)
    = FromDefinition Text (Maybe (Lexeme Text)) -- Symbol name and definition site
    | FromContext (ErrorInfo p)                     -- Context where binding happened
    | FromInference (Node (Lexeme Text))         -- Expression that caused inference
    | Builtin                                   -- Language builtin
    deriving (Show, Generic)

-- instance ToJSON Provenance -- ErrorInfo doesn't have ToJSON yet, might be complex due to Doc

-- | Structured type error
data TypeError (p :: Phase)
    = TypeMismatch (TypeInfo p) (TypeInfo p) MismatchReason (Maybe (MismatchDetail p))
    | UndefinedVariable Text
    | UndefinedType Text
    | MemberNotFound Text (TypeInfo p)
    | NotAStruct (TypeInfo p)
    | TooManyArgs { expectedCount :: Int, actualCount :: Int }
    | TooFewArgs { expectedCount :: Int, actualCount :: Int }
    | NotALValue
    | CallingNonFunction Text (TypeInfo p)
    | SwitchConditionNotIntegral (TypeInfo p)
    | DereferencingNonPointer (TypeInfo p)
    | ArrayAccessNonArray (TypeInfo p)
    | MacroArgumentMismatch Text Int Int -- Name, expected, actual
    | MissingReturnValue (TypeInfo p)
    | InfiniteType Text (TypeInfo p)
    | UnhandledConstruct Text
    | CustomError Text
    | RefinedVariantMismatch
    | RefinedNullabilityMismatch
    deriving (Show, Generic)

instance ToJSON (TypeError p)

-- | Error information with context
data ErrorInfo (p :: Phase) = ErrorInfo
    { errLoc         :: Maybe (Lexeme Text)
    , errContext     :: [Context p]
    , errType        :: TypeError p
    , errExplanation :: [Doc AnsiStyle]
    }
    deriving (Show, Generic)

instance ToJSON (ErrorInfo p) where
    toJSON ErrorInfo{..} = object
        [ "loc" .= errLoc
        , "context" .= errContext
        , "type" .= errType
        , "explanation" .= map (TR.renderStrict . layoutPretty defaultLayoutOptions . unAnnotate) errExplanation
        ]
