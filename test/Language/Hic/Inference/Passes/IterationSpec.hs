{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Inference.Passes.IterationSpec
    ( spec
    ) where

import           Language.Hic.Inference.Engine     (inferProgram)
import           Language.Hic.Inference.EngineSpec (checkInference, mustParse)
import           Test.Hspec                        (Spec, describe, it,
                                                    shouldBe)

spec :: Spec
spec = do
    describe "ForEach" $ do
        checkInference
            [ "void f() {"
            , "    for (int i = 0; i < 10; ++i) {"
            , "        printf(\"%d\\n\", arr[i]);"
            , "    }"
            , "}"
            ]
            [ "void f() {"
            , "  for_each i in arr {"
            , "    printf(\"%d\\n\", i);"
            , "  }"
            , "}"
            ]

        checkInference
            [ "void f() {"
            , "    for (int i = 0; i < 10; ++i) {"
            , "        printf(\"%d: %d\\n\", i, arr[i]);"
            , "    }"
            , "}"
            ]
            [ "void f() {"
            , "  for_each (index, i) in enumerate(arr) {"
            , "    printf(\"%d: %d\\n\", index, i);"
            , "  }"
            , "}"
            ]

        checkInference
            [ "uint64_t calculate_comp_value(const uint8_t *pk1, const uint8_t *pk2) {"
            , "    uint64_t cmp1 = 0;"
            , "    uint64_t cmp2 = 0;"
            , "    for (size_t i = 0; i < 8; ++i) {"
            , "        cmp1 = (cmp1 << 8) + (uint64_t)pk1[i];"
            , "        cmp2 = (cmp2 << 8) + (uint64_t)pk2[i];"
            , "    }"
            , "    return cmp1 - cmp2;"
            , "}"
            ]
            [ "uint64_t calculate_comp_value(uint8_t const* pk1, uint8_t const* pk2) {"
            , "  uint64_t cmp1 = 0;"
            , ""
            , "  uint64_t cmp2 = 0;"
            , ""
            , "  for_each index in (pk1, pk2) {"
            , "    cmp1 = (cmp1 << 8) + (uint64_t)pk1[index];"
            , ""
            , "    cmp2 = (cmp2 << 8) + (uint64_t)pk2[index];"
            , "  }"
            , ""
            , "  return cmp1 - cmp2;"
            , "}"
            ]

        checkInference
            [ "void f() {"
            , "    for (uint32_t i = 0; i < c->crypto_connections_length; ++i) {"
            , "        process(c->crypto_connections[i]);"
            , "    }"
            , "}"
            ]
            [ "void f() {"
            , "  for_each i in c->crypto_connections {"
            , "    process(i);"
            , "  }"
            , "}"
            ]

        checkInference
            [ "void f() {"
            , "    for (int i = 0; i < 10; ++i) {"
            , "        arr[i] = i;"
            , "    }"
            , "}"
            ]
            [ "void f() {"
            , "  for_each (index, i) in enumerate(arr) {"
            , "    i = index;"
            , "  }"
            , "}"
            ]

        it "warns when induction variable is modified" $ do
            prog <- mustParse
                [ "void f() {"
                , "    for (int i = 0; i < 10; ++i) {"
                , "        arr[i] = 0;"
                , "        i = 5;"
                , "    }"
                , "}"
                ]
            let (_, diags) = inferProgram prog
            diags `shouldBe` ["test.c:2: Induction variable 'i' is modified within the loop body. Refactor to enable for_each lifting."]

        checkInference
            [ "void f() {"
            , "    for (int i = 0; i < 10; ++i) {"
            , "        arr[i] = 0;"
            , "        arr2[i] = 1;"
            , "    }"
            , "}"
            ]
            [ "void f() {"
            , "  for_each index in (arr, arr2) {"
            , "    arr[index] = 0;"
            , ""
            , "    arr2[index] = 1;"
            , "  }"
            , "}"
            ]

        it "warns when container expression is not stable" $ do
            prog <- mustParse
                [ "void f(int matrix[10][10], int j) {"
                , "    for (int i = 0; i < 10; ++i) {"
                , "        matrix[j][i] = 0;"
                , "    }"
                , "}"
                ]
            let (_, diags) = inferProgram prog
            diags `shouldBe` ["test.c:2: Container expression is not stable. Refactor to enable for_each lifting."]

        checkInference
            [ "void f(int matrix[10][10], int j) {"
            , "    int *row = matrix[j];"
            , "    for (int i = 0; i < 10; ++i) {"
            , "        row[i] = 0;"
            , "    }"
            , "}"
            ]
            [ "void f(int matrix[10][10], int j) {"
            , "  int* row = matrix[j];"
            , ""
            , "  for_each i in row {"
            , "    i = 0;"
            , "  }"
            , "}"
            ]

    describe "Find" $ do
        checkInference
            [ "int find(int *arr, int size, int key) {"
            , "    for (int i = 0; i < size; ++i) {"
            , "        if (arr[i] == key) return i;"
            , "    }"
            , "    return -1;"
            , "}"
            ]
            [ "int find(int* arr, int size, int key) {"
            , "  find i in arr where i == key {"
            , "    return index;"
            , "  } else {"
            , "    return -1;"
            , "  }"
            , "}"
            ]

        checkInference
            [ "int find_wrapped(int *arr, int size, int key) {"
            , "    for (int i = 0; i < size; ++i) {"
            , "        if (arr[i] == key) {"
            , "            return i;"
            , "        }"
            , "    }"
            , "    return -1;"
            , "}"
            ]
            [ "int find_wrapped(int* arr, int size, int key) {"
            , "  find i in arr where i == key {"
            , "    return index;"
            , "  } else {"
            , "    return -1;"
            , "  }"
            , "}"
            ]

