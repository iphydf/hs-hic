{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData    #-}

module Language.Hic.Refined.Registry
    ( Registry (..)
    , TypeDefinition (..)
    , Member (..)
    ) where

import           Data.Map.Strict                (Map)
import           Data.Text                      (Text)
import           GHC.Generics                   (Generic)
import           Language.Cimple                (Lexeme (..))
import           Language.Hic.Refined.LatticeOp (Variance (..))
import           Language.Hic.Refined.Types     (TemplateId)

-- | The Registry stores the formal definitions of all nominal types.
-- It is the source of truth for struct arity and structural links.
data Registry a = Registry
    { regDefinitions :: Map Text (TypeDefinition a)
    }
    deriving (Show, Eq, Ord, Generic)

-- | Formal definition of a Nominal type.
data TypeDefinition a
    = StructDef
        { sdName       :: Lexeme Text
        , sdParameters :: [(TemplateId, Variance)] -- ^ Structural parameters with variance
        , sdMembers    :: [Member a]              -- ^ Internal fields
        }
    | UnionDef
        { udName       :: Lexeme Text
        , udParameters :: [(TemplateId, Variance)]
        , udMembers    :: [Member a]
        }
    | EnumDef
        { edName    :: Lexeme Text
        , edMembers :: [Lexeme Text]
        }
    deriving (Show, Eq, Ord, Generic)

-- | A member field within a struct or union.
data Member a = Member
    { mName :: Lexeme Text
    , mType :: a -- ^ Type reference (ID or Symbolic)
    }
    deriving (Show, Eq, Ord, Generic)
