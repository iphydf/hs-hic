{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Inference.Passes.ScopedSpec (spec) where

import           Language.Hic.Inference.EngineSpec (checkInference)
import           Test.Hspec                        (Spec, describe)

spec :: Spec
spec = do
    checkInference
        [ "void f(int something_wrong) {"
        , "    Tox *tox = tox_new(nullptr, nullptr);"
        , "    if (!tox) return;"
        , "    if (something_wrong) {"
        , "        goto CLEANUP;"
        , "    }"
        , "    process(tox);"
        , "CLEANUP:"
        , "    tox_kill(tox);"
        , "}"
        ]
        [ "void f(int something_wrong) {"
        , "  scoped (Tox* tox = tox_new(nullptr, nullptr)) {"
        , "    if (!tox) return;"
        , "    if (something_wrong) {"
        , "      goto CLEANUP;"
        , "    }"
        , "    process(tox);"
        , "  CLEANUP: tox_kill(tox);"
        , "  }"
        , "}"
        ]
