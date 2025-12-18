{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TestUtils
    ( mustParse
    , mustParseNodes
    ) where

import           Data.Text               (Text)
import qualified Data.Text               as T
import           GHC.Stack               (HasCallStack)

import qualified Language.Cimple         as C
import qualified Language.Cimple.IO      as C
import qualified Language.Cimple.Program as C

mustParse :: (HasCallStack, MonadFail m) => [Text] -> m (C.Program Text)
mustParse code =
    case C.parseText $ T.unlines code of
        Left err -> fail err
        Right nodes -> case C.fromList [("test.c", nodes)] of
            Left err -> fail err
            Right ok -> return ok

mustParseNodes :: (HasCallStack, MonadFail m) => [Text] -> m [C.Node (C.Lexeme Text)]
mustParseNodes code = do
    prog <- mustParse code
    case lookup "test.c" (C.toList prog) of
        Just nodes -> return nodes
        Nothing    -> fail "expected test.c in program"
