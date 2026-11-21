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
    , NullUse(..)
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
    | CastMismatch
    deriving (Show, Eq, Ord, Generic)

instance Arbitrary MismatchReason where
    arbitrary = oneof
        [ return GeneralMismatch
        , return ReturnMismatch
        , ArgumentMismatch <$> arbitrary
        , return AssignmentMismatch
        , return InitializerMismatch
        , return CastMismatch
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
    | RefinedCastMismatch -- ^ A cast between types that don't fit each other.
    | ArgumentTooShort Text Int Integer (Maybe Integer)
      -- ^ A call whose argument can't be shown to have the elements its array
      -- parameter needs: function, argument number (from 1), elements needed,
      -- and how many it's known to have.
    | ArgumentTooSmall Text Int Integer (Maybe Integer)
      -- ^ A call whose integer argument can't be shown to be as big as the
      -- function needs (a length its buffers are measured by): function,
      -- argument number (from 1), the least it needs, and the least it's
      -- known to be.
    | ArgumentTooBig Text Int Integer (Maybe Integer)
      -- ^ A call whose integer argument can't be shown to be as small as the
      -- function needs (a length of what it copies into a buffer of its
      -- own): function, argument number (from 1), the most it can be, and
      -- the most it's known to be.
    | PointeeTooBig Text Int Integer (Maybe Integer)
      -- ^ A call whose argument points to an integer that can't be shown to
      -- be as small as the function needs where it starts (a count it goes
      -- on with): function, argument number (from 1), the most it can be,
      -- and the most it's known to be.
    | ArgumentsUnbalanced Text [(Integer, Int)] Integer (Maybe Integer)
      -- ^ A call whose integer arguments can't be shown to be what the
      -- function needs of each other: function, the sum (so many times each
      -- argument number, from 1, and a number) that must be at least 0, and
      -- the least it's known to be.
    | SignedOverflow (Maybe Integer) (Maybe Integer) Integer Integer
      -- ^ Signed arithmetic whose result can't be shown to fit its type,
      -- which is undefined: the least and most the numbers can give, and the
      -- least and most the type holds.
    | AssertMayFail Text
      -- ^ An assert on integers whose condition can't be shown to hold
      -- where it is: the condition, as written.
    | PlatformOutsideItsLayer Text
      -- ^ One of the operating system's types or functions used outside
      -- the platform layer (the @os_@ files): its name.
    | NegativeToUnsigned Text Text (Maybe Integer)
      -- ^ A signed number that can't be shown not to be negative where it's
      -- converted to an unsigned type, which changes it: as written, the
      -- type, and the least it can be.
    | TooBigForSigned Text Text (Maybe Integer)
      -- ^ An unsigned number that can't be shown to fit where it's converted
      -- to a signed type, which changes it: as written, the type, and the
      -- most it can be.
    | IndexOutOfBounds Text Text (Maybe Integer) (Maybe Integer) (Maybe Integer)
      -- ^ An index that can't be shown to be in bounds: the array (or
      -- pointer) and the index as written, how many elements it's known to
      -- have, and the least and most the index can be.
    | PointerPastEnd Text Text (Maybe Integer) (Maybe Integer) (Maybe Integer)
      -- ^ A pointer moved by an amount that can't be shown to keep it in its
      -- buffer or just past its end: the pointer and the amount as written,
      -- how many elements it's known to have, and the least and most the
      -- amount can be.
    | MayBeNull Text NullUse Bool
      -- ^ A pointer that can't be shown not to be null where it must not
      -- be: as written, where it's used, and whether it's null for sure.
    | ArgumentShorterThanLength Text Int Int (Maybe Integer) (Maybe Integer)
      -- ^ A call whose buffer argument can't be shown to have as many
      -- elements as the length argument passed with it says: function, the
      -- buffer's and the length's argument numbers (from 1), how many
      -- elements the buffer is known to have, and the most the length can be.
    | ArgumentShorterThanNeeded Text Int (Maybe Integer) (Maybe Integer)
      -- ^ A call whose buffer argument can't be shown to have as many
      -- elements as the function needs of it, from what it does with it:
      -- function, argument number (from 1), how many elements it's known to
      -- have, and the most the function may need.
    | BufferShorterThanLength Text Text (Maybe Integer) (Maybe Integer)
      -- ^ A buffer kept with its length (a field and its length field, or
      -- what out-parameters for both point to) that can't be shown to have
      -- as many elements as the length says where something else can see
      -- them: both as written, how many elements the buffer is known to
      -- have, and the most the length can be.
    | CountAboveCapacity Text Text
      -- ^ An array's count field that can't be shown to be at most its
      -- capacity field where something else can see them, both as written.
    deriving (Show, Generic)

instance ToJSON (TypeError p)

-- | Where a pointer must not be null.
data NullUse
    = Dereferenced
    | Called
    | ArgumentOf Text Int
      -- ^ A function's parameter that is @_Nonnull@: the function, and the
      -- argument number (from 1).
    | StoredIn Text
      -- ^ A place declared @_Nonnull@, as written.
    | ReturnedFrom Text
      -- ^ A function whose result is declared @_Nonnull@.
    deriving (Show, Eq, Ord, Generic)

instance ToJSON NullUse

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
