{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Hic.Refined.ContextSpec (spec) where

import           Control.Exception              (evaluate)
import           Data.Bits                      (shiftR, (.&.))
import           Data.Word                      (Word32)
import           Language.Hic.Refined.Arbitrary ()
import           Language.Hic.Refined.Context
import           Test.Hspec
import           Test.Hspec.QuickCheck          (prop)
import           Test.QuickCheck                ((===))

spec :: Spec
spec = do
    describe "MappingContext" $ do
        it "starts empty" $ do
            getMapping 0 emptyContext `shouldBe` Nothing

        it "can push and retrieve a mapping" $ do
            let ctx = pushMapping 5 emptyContext
            getMapping 0 ctx `shouldBe` Just 5
            getMapping 1 ctx `shouldBe` Nothing

        it "can store multiple mappings" $ do
            let ctx = pushMapping 3 $ pushMapping 7 emptyContext
            getMapping 0 ctx `shouldBe` Just 3
            getMapping 1 ctx `shouldBe` Just 7
            getMapping 2 ctx `shouldBe` Nothing

        it "supports up to 15 mappings (due to 60/4)" $ do
            let ctx = foldl (flip pushMapping) emptyContext [0..14]
            getMapping 0 ctx `shouldBe` Just 14
            getMapping 14 ctx `shouldBe` Just 0
            getMapping 15 ctx `shouldBe` Nothing

        it "saturates at 30 mappings (due to 128-bit structure)" $ do
            -- The count field (bits 0-7) is capped at 30.
            let ctx = foldl (flip pushMapping) emptyContext [0..30]
            getMapping 29 ctx `shouldBe` Just 1
            getMapping 30 ctx `shouldBe` Nothing

        prop "last pushed mapping is at index 0" $ \m (ctx :: MappingContext) ->
            getMapping 0 (pushMapping m ctx) == Just (m `mod` 16)

        prop "pushing preserves existing mappings at shifted indices" $ \m (ctx :: MappingContext) ->
            let newCtx = pushMapping m ctx
                check i = getMapping (i + 1) newCtx == getMapping i ctx
            in all check [0..13]

        prop "getMapping returns Nothing for index >= count" $ \ctx ->
            let MappingContext w1 _ = ctx
                count = fromIntegral (w1 .&. 0xFF)
            in all (\i -> getMapping i ctx == Nothing) [count..29]

    describe "MappingRefinements" $ do
        it "starts empty" $ do
            getRefinement 0 emptyRefinements `shouldBe` Nothing

        it "can set and get refinements" $ do
            let refs = setRefinement 123 456 emptyRefinements
            getRefinement 123 refs `shouldBe` Just 456
            getRefinement 124 refs `shouldBe` Nothing

        it "can store many refinements" $ do
            let refs = foldl (\r i -> setRefinement i (fromIntegral i + 10) r) emptyRefinements [0..1000]
            getRefinement 0 refs `shouldBe` Just 10
            getRefinement 1000 refs `shouldBe` Just 1010

        prop "set and get refinement" $ \key (nodeID :: Word32) ->
            let n = nodeID .&. 0x3FFFFFFF
                refs' = setRefinement key n emptyRefinements
            in getRefinement key refs' === Just n


