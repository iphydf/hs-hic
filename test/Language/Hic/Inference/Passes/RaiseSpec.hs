{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Inference.Passes.RaiseSpec (spec) where

import           Language.Hic.Inference.EngineSpec (checkInference)
import           Test.Hspec                        (Spec, describe)

spec :: Spec
spec = do
    checkInference
        [ "int f(int *error) {"
        , "    if (error) {"
        , "        *error = 1;"
        , "        return -1;"
        , "    }"
        , "    return 0;"
        , "}"
        ]
        [ "int f(int* error) {"
        , "  if (error) {"
        , "    raise(*error, 1) return -1;"
        , "  }"
        , ""
        , "  return 0;"
        , "}"
        ]
