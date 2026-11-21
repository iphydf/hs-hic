{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}

-- | Places in memory followed like variables: a variable's fields, the
-- elements of arrays in them at a variable or constant, and what pointers
-- in them point to.
module Language.Hic.Refined.BufferSize.Paths
    ( Step (..)
    , Path (..)
    , pathOf
    , pathName
    , pathVars
    , isPartOf
    , isThrough
    ) where

import           Data.Fix        (Fix (..))
import           Data.List       (isPrefixOf)
import           Data.Text       (Text)
import           Language.Cimple (Lexeme (..), NodeF (..))
import qualified Language.Cimple as C

data Step
    = Field Text
    | Deref
    | Index Text Bool
      -- ^ An element, at a variable ('True') or a constant.
    deriving (Show, Eq, Ord)

data Path = Path
    { pathRoot  :: Text
    , pathSteps :: [Step]
    }
    deriving (Show, Eq, Ord)

pathOf :: C.Node (Lexeme Text) -> Maybe Path
pathOf (Fix node) = case node of
    VarExpr (L _ _ v)                             -> Just (Path v [])
    ParenExpr e                                   -> pathOf e
    PointerAccess b (L _ _ f)                     -> step [Deref, Field f] b
    MemberAccess b (L _ _ f)                      -> step [Field f] b
    UnaryExpr C.UopDeref b                        -> step [Deref] b
    ArrayAccess b (Fix (VarExpr (L _ _ i)))       -> step [Index i True] b
    ArrayAccess b (Fix (LiteralExpr _ (L _ _ i))) -> step [Index i False] b
    _                                             -> Nothing
  where
    step s b = (\p -> p { pathSteps = pathSteps p ++ s }) <$> pathOf b

-- | A path as C writes it.
pathName :: Path -> Text
pathName (Path root steps) = go root steps
  where
    go acc = \case
        Deref : Field f : rest -> go (acc <> "->" <> f) rest
        [Deref]                -> "*" <> acc
        Deref : rest           -> go ("(*" <> acc <> ")") rest
        Field f : rest         -> go (acc <> "." <> f) rest
        Index i _ : rest       -> go (acc <> "[" <> i <> "]") rest
        []                     -> acc

-- | The variables a path's place depends on.
pathVars :: Path -> [Text]
pathVars (Path root steps) = root : [ i | Index i True <- steps ]

-- | Whether a path is in the place another one is: it or a part of it.
isPartOf :: Path -> Path -> Bool
isPartOf q p = pathRoot q == pathRoot p && pathSteps p `isPrefixOf` pathSteps q

-- | Whether a path is in memory a pointer (or array) value points to.
isThrough :: Path -> Path -> Bool
isThrough q p = q `isPartOf` p && case drop (length (pathSteps p)) (pathSteps q) of
    Deref : _   -> True
    Index{} : _ -> True
    _           -> False
