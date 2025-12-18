{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Ordered.HotspotAnalysis
    ( GlobalAnalysisResult (..)
    , GenericHotspot (..)
    , runGlobalStructuralAnalysis
    ) where

import           Data.Aeson                        (ToJSON)
import qualified Data.Map.Strict                   as Map
import           Data.Set                          (Set)
import qualified Data.Set                          as Set
import           Data.Text                         (Text)
import           GHC.Generics                      (Generic)
import qualified Language.Cimple.Program           as Program
import           Language.Hic.Core.TypeSystem      (TypeDescr (..), TypeSystem)
import           Language.Hic.TypeSystem.Core.Base (isGeneric)
import qualified Language.Hic.TypeSystem.Core.Base as TypeSystem

data GenericHotspot
    = StructHotspot Text -- Struct contains void* or templates
    | FunctionHotspot Text -- Function signature uses void* or templates
    deriving (Show, Eq, Ord, Generic)

instance ToJSON GenericHotspot

data GlobalAnalysisResult = GlobalAnalysisResult
    { garTypeSystem :: TypeSystem
    , garHotspots   :: Set GenericHotspot
    } deriving (Show, Generic)

instance ToJSON GlobalAnalysisResult

runGlobalStructuralAnalysis :: Program.Program Text -> GlobalAnalysisResult
runGlobalStructuralAnalysis program =
    let programList = Program.toList program
        ts = TypeSystem.collect programList
        hotspots = findHotspots ts
    in GlobalAnalysisResult ts hotspots

findHotspots :: TypeSystem -> Set GenericHotspot
findHotspots ts =
    let structHotspots = Map.foldlWithKey' checkStruct Set.empty ts
        funcHotspots = Map.foldlWithKey' checkFunc Set.empty ts
    in Set.union structHotspots funcHotspots
  where
    checkStruct acc name descr =
        case descr of
            StructDescr _ _ members _ | any (isGeneric . snd) members ->
                Set.insert (StructHotspot name) acc
            UnionDescr _ _ members _ | any (isGeneric . snd) members ->
                Set.insert (StructHotspot name) acc
            _ -> acc

    checkFunc acc name descr =
        case descr of
            FuncDescr _ _ ret params | isGeneric ret || any isGeneric params ->
                Set.insert (FunctionHotspot name) acc
            _ -> acc
