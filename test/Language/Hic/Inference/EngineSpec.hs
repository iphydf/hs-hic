{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Inference.EngineSpec
    ( checkInference
    , checkRefactoring
    , mustParse
    , mustParseNodes
    , spec
    ) where

import           Data.Fix                      (Fix (..))
import           Data.Map.Strict               (Map)
import qualified Data.Map.Strict               as Map
import           Data.Maybe                    (fromMaybe)
import           Data.Text                     (Text)
import qualified Data.Text                     as T
import           GHC.Stack                     (HasCallStack)
import           Test.Hspec                    (Spec, describe, it, shouldBe,
                                                shouldContain)

import qualified Language.Cimple               as C
import qualified Language.Cimple.IO            as C
import qualified Language.Cimple.Program       as C
import           Language.Hic.Ast              as H
import           Language.Hic.Inference        (lower)
import           Language.Hic.Inference.Engine (inferProgram)
import           Language.Hic.Pretty           (showNodePlain)
import           Language.Hic.TestUtils        (mustParse, mustParseNodes)

checkInference :: HasCallStack => [Text] -> [Text] -> Spec
checkInference input expectedHic = checkRefactoring input expectedHic input

checkRefactoring :: HasCallStack => [Text] -> [Text] -> [Text] -> Spec
checkRefactoring input expectedHic expectedRefactored =
    let desc = case input of
            (x:_) -> T.unpack x
            []    -> "empty input"
    in it desc $ do
    prog <- mustParse input
    let (hicAsts, diags) = inferProgram prog
    diags `shouldBe` []
    hicNodes <- case Map.lookup "test.c" hicAsts of
        Just nodes | not (null nodes) -> return nodes
        _                             -> fail "expected at least one hic node"

    -- Check pretty-printed Hic
    let printed = T.intercalate "\n" $ map showNodePlain hicNodes
    printed `shouldBe` T.intercalate "\n" expectedHic

    -- Check reversibility against refactored version
    let lowered = map lower hicNodes
    refactoredNodes <- mustParseNodes expectedRefactored
    map (C.removeSloc . C.elideGroups) lowered `shouldBe` map (C.removeSloc . C.elideGroups) refactoredNodes

spec :: Spec
spec = do
    it "combines multiple inference features" $ do
        prog <- mustParse
            [ "typedef enum Tox_Event_Type { TOX_EVENT_FRIEND_MESSAGE } Tox_Event_Type;"
            , "typedef union Tox_Event_Data { struct Tox_Event_Friend_Message *friend_message; } Tox_Event_Data;"
            , "struct Tox_Event { Tox_Event_Type type; Tox_Event_Data data; };"
            , "void handle_events(struct Tox_Event *events, int count) {"
            , "    for (int i = 0; i < count; ++i) {"
            , "        switch (events[i].type) {"
            , "            case TOX_EVENT_FRIEND_MESSAGE: {"
            , "                handle_message(events[i].data.friend_message);"
            , "                break;"
            , "            }"
            , "        }"
            , "    }"
            , "}"
            ]
        let (hicAsts, diags) = inferProgram prog
        diags `shouldBe` []
        hicNodes <- case Map.lookup "test.c" hicAsts of
            Just nodes -> return nodes
            _          -> fail "expected test.c in program"

        let printed = T.unpack $ T.intercalate "\n" $ map showNodePlain hicNodes
        -- We expect a ForEach containing a Match
        printed `shouldContain` "for_each i in events"
        printed `shouldContain` "match i {"
        printed `shouldContain` "TOX_EVENT_FRIEND_MESSAGE => {"
        printed `shouldContain` "handle_message(i.friend_message);"

-- end of tests
