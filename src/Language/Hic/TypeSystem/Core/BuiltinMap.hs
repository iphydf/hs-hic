{-# LANGUAGE DataKinds #-}
module Language.Hic.TypeSystem.Core.BuiltinMap
    ( builtinMap
    ) where

import           Data.Map.Strict                       (Map)
import qualified Data.Map.Strict                       as Map
import           Data.Text                             (Text)
import           Language.Hic.Core.TypeSystem          (Origin (..), Phase (..),
                                                        TypeInfo)
import           Language.Hic.TypeSystem.Core.Base     (descrToTypeInfo,
                                                        toLocal)
import           Language.Hic.TypeSystem.Core.Builtins (builtins)

builtinMap :: Map Text (TypeInfo 'Local)
builtinMap = Map.map (toLocal 0 TopLevel . descrToTypeInfo) builtins
