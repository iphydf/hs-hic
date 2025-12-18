{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData          #-}
module Language.Hic.Inference.Program.Types
    ( Program (..)
    ) where

import           Data.Bifunctor   (bimap)
import           Data.Fix         (hoistFix)
import           Data.Map.Strict  (Map)
import qualified Data.Map.Strict  as Map
import           Data.Text        (Text)
import           Language.Hic.Ast (Node)

data Program lexeme = Program
    { progAsts        :: Map FilePath [Node lexeme]
    , progDiagnostics :: [Text]
    }

instance Functor Program where
    fmap (f :: a -> b) p = p { progAsts = Map.map (map (hoistFix (bimap f id))) (progAsts p) }
