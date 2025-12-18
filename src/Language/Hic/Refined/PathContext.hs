{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

module Language.Hic.Refined.PathContext
    ( PathContext (..)
    , SymbolicPath (..)
    , PathRoot (..)
    , PathStep (..)
    , ValueConstraint (..)
    , emptyPath
    , extendPath
    , simplifyPath
    ) where

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Text       (Text)
import           GHC.Generics    (Generic)

-- | The PathContext tracks the symbolic state of the program within a scope.
-- It maps memory paths to their known refinements and tracks pointer aliases.
data PathContext = PathContext
    { pcRefinements :: Map SymbolicPath ValueConstraint
    , pcAliases     :: Map Text SymbolicPath -- ^ Lexical Alias Tracking (m2 = m1)
    }
    deriving (Show, Eq, Ord, Generic)

-- | A symbolic reference to a memory location or instance.
data SymbolicPath = SymbolicPath
    { spRoot  :: PathRoot
    , spSteps :: [PathStep]
    }
    deriving (Show, Eq, Ord, Generic)

-- | Initial empty path.
emptyPath :: SymbolicPath
emptyPath = SymbolicPath (VarRoot "") []

-- | Extends a symbolic path with a new step.
extendPath :: PathStep -> SymbolicPath -> SymbolicPath
extendPath step p = p { spSteps = spSteps p ++ [step] }

-- | Simplifies nested paths (e.g., following an alias).
simplifyPath :: Map Text SymbolicPath -> SymbolicPath -> SymbolicPath
simplifyPath aliases p =
    case spRoot p of
        VarRoot v ->
            case Map.lookup v aliases of
                Just base ->
                    -- Substitute root and prepend its steps
                    SymbolicPath (spRoot base) (spSteps base ++ spSteps p)
                Nothing -> p
        _ -> p

-- | The starting point of a symbolic path.
data PathRoot
    = VarRoot Text      -- ^ Local variable
    | ParamRoot Int     -- ^ Function parameter (for inter-procedural mapping)
    | InstanceRoot Integer -- ^ Absolute unique Instance ID
    deriving (Show, Eq, Ord, Generic)

-- | Steps in a symbolic path.
data PathStep
    = FieldStep Text    -- ^ p->field
    | IndexStep Integer -- ^ arr[0] (Literal)
    | VarStep Text      -- ^ arr[i] (Symbolic index variable)
    deriving (Show, Eq, Ord, Generic)

-- | Known symbolic values discovered via control flow (if/switch).
data ValueConstraint
    = EqConst Integer
    | NotConst Integer
    | EqVariant Integer -- ^ Index of the union member
    deriving (Show, Eq, Ord, Generic)
