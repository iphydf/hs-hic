{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData          #-}
module Language.Hic.Inference.Program
    ( Program (..)
    , fromCimple
    , toCimple
    ) where

import           Data.Map.Strict                      (Map)
import qualified Data.Map.Strict                      as Map
import           Data.Text                            (Text)
import qualified Language.Cimple                      as C
import qualified Language.Cimple.Program              as Program
import           Language.Hic.Ast                     (NodeF (..))
import           Language.Hic.Inference               (lower)
import           Language.Hic.Inference.Engine        (inferProgram)
import           Language.Hic.Inference.Program.Types (Program (..))

-- | Converts a standard Cimple Program to a high-level Hic Program.
-- This is where global inference happens.
fromCimple :: Program.Program Text -> Program (C.Lexeme Text)
fromCimple cprog =
    let (hicAsts, diags) = inferProgram cprog
    in Program
        { progAsts = hicAsts
        , progDiagnostics = diags
        }

-- | Lowers a Hic Program back to a standard Cimple Program.
toCimple :: Program (C.Lexeme Text) -> Program.Program Text
toCimple Program{..} =
    case Program.fromList (Map.toList $ Map.map (map lower) progAsts) of
        Left err -> error $ "Hic.toCimple: " ++ err
        Right p  -> p
