{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Refined.Inference.Utils where

import qualified Debug.Trace as Debug

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()
