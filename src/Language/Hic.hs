{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData          #-}
module Language.Hic
    ( module Language.Hic.Inference
    , module Language.Hic.TypeSystem.Standard.Base
    , module Language.Hic.Refined.Inference
    -- * Hic Driver
    , Phase (..)
    , HicState (..)
    , executePhase
    , runToPhase
    , emptyState
    ) where

import           Control.Exception                                    (evaluate)
import           Control.Monad                                        (foldM)
import           Data.Aeson                                           (ToJSON)
import qualified Data.Map.Strict                                      as Map
import qualified Data.Set                                             as Set
import           Data.Maybe                                           (fromJust,
                                                                       isJust)
import           Data.Text                                            (Text)
import           Data.Time.Clock                                      (diffUTCTime,
                                                                       getCurrentTime)
import           GHC.Generics                                         (Generic)
import           Text.Printf                                          (printf)

import qualified Language.Cimple.Program                              as Program
import           Language.Hic.Inference
import           Language.Hic.Refined.Inference
import           Language.Hic.TypeSystem.Standard.Base

import           Language.Hic.Core.TypeSystem                         (TypeSystem)
import           Language.Hic.TypeSystem.Ordered.ArrayUsage           (ArrayUsageResult (..),
                                                                       runArrayUsageAnalysis)
import           Language.Hic.TypeSystem.Ordered.Base                 (OrderedSolverResult (..),
                                                                       runOrderedSolver)
import           Language.Hic.TypeSystem.Ordered.CallGraph            (CallGraphResult (..),
                                                                       runCallGraphAnalysis)
import           Language.Hic.TypeSystem.Ordered.ConstraintGeneration (ConstraintGenResult (..),
                                                                       runConstraintGeneration)
import           Language.Hic.TypeSystem.Ordered.HotspotAnalysis      (GlobalAnalysisResult (..),
                                                                       runGlobalStructuralAnalysis)
import           Language.Hic.TypeSystem.Ordered.Invariants           (InvariantResult (..),
                                                                       runInvariantAnalysis)
import           Language.Hic.TypeSystem.Ordered.Nullability          (NullabilityResult (..),
                                                                       runNullabilityAnalysis)

data Phase
    = PhaseGlobalStructural
    | PhaseArrayUsage
    | PhaseCallGraph
    | PhaseInvariants
    | PhaseNullability
    | PhaseConstraintGen
    | PhaseSolving
    deriving (Show, Eq, Ord, Enum, Bounded, Generic)

instance ToJSON Phase

data HicState = HicState
    { hsProgram       :: Program.Program Text
    , hsGlobalStruct  :: Maybe GlobalAnalysisResult
    , hsArrayUsage    :: Maybe ArrayUsageResult
    , hsCallGraph     :: Maybe CallGraphResult
    , hsInvariants    :: Maybe InvariantResult
    , hsNullability   :: Maybe NullabilityResult
    , hsConstraintGen :: Maybe ConstraintGenResult
    , hsOrderedResult :: Maybe OrderedSolverResult
    } deriving (Generic)

emptyState :: Program.Program Text -> HicState
emptyState prog = HicState prog Nothing Nothing Nothing Nothing Nothing Nothing Nothing

type Logger = String -> IO ()

runToPhase :: Logger -> Phase -> HicState -> IO HicState
runToPhase logger targetPhase state = foldM (executePhase logger) state [minBound .. targetPhase]

executePhase :: Logger -> HicState -> Phase -> IO HicState
executePhase logger state phase = case phase of
    PhaseGlobalStructural | isJust (hsGlobalStruct state) -> return state
    PhaseGlobalStructural -> do
        logger "Phase: Global Structural Analysis..."
        start <- getCurrentTime
        let res = runGlobalStructuralAnalysis (hsProgram state)
        _ <- evaluate (Map.size (garTypeSystem res) + Set.size (garHotspots res))
        end <- getCurrentTime
        logger $ printf " (%.3fs)\n" (realToFrac (diffUTCTime end start) :: Double)
        return state { hsGlobalStruct = Just res }

    PhaseArrayUsage | isJust (hsArrayUsage state) -> return state
    PhaseArrayUsage -> do
        s1 <- executePhase logger state PhaseGlobalStructural
        logger "Phase: Array Usage Analysis..."
        start <- getCurrentTime
        let ts = garTypeSystem $ fromJust $ hsGlobalStruct s1
            res = runArrayUsageAnalysis ts (hsProgram s1)
        _ <- evaluate (Map.size (aurFlavors res))
        end <- getCurrentTime
        logger $ printf " (%.3fs)\n" (realToFrac (diffUTCTime end start) :: Double)
        return s1 { hsArrayUsage = Just res }

    PhaseCallGraph | isJust (hsCallGraph state) -> return state
    PhaseCallGraph -> do
        logger "Phase: Call Graph Analysis..."
        start <- getCurrentTime
        let res = runCallGraphAnalysis (hsProgram state)
        _ <- evaluate (Map.size (cgrDirectCalls res) + length (cgrSccs res))
        end <- getCurrentTime
        logger $ printf " (%.3fs)\n" (realToFrac (diffUTCTime end start) :: Double)
        return state { hsCallGraph = Just res }

    PhaseInvariants | isJust (hsInvariants state) -> return state
    PhaseInvariants -> do
        s1 <- executePhase logger state PhaseGlobalStructural
        s2 <- executePhase logger s1 PhaseCallGraph
        logger "Phase: Structural Invariant Discovery..."
        start <- getCurrentTime
        let ts = garTypeSystem $ fromJust $ hsGlobalStruct s2
            sccs = cgrSccs $ fromJust $ hsCallGraph s2
            res = runInvariantAnalysis ts sccs (hsProgram s2)
        _ <- evaluate (Map.size (irInvariants res))
        end <- getCurrentTime
        logger $ printf " (%.3fs)\n" (realToFrac (diffUTCTime end start) :: Double)
        return s2 { hsInvariants = Just res }

    PhaseNullability | isJust (hsNullability state) -> return state
    PhaseNullability -> do
        logger "Phase: Nullability Analysis..."
        start <- getCurrentTime
        let res = runNullabilityAnalysis (hsProgram state)
        _ <- evaluate (Map.size (nrFunctionFacts res))
        end <- getCurrentTime
        logger $ printf " (%.3fs)\n" (realToFrac (diffUTCTime end start) :: Double)
        return state { hsNullability = Just res }

    PhaseConstraintGen | isJust (hsConstraintGen state) -> return state
    PhaseConstraintGen -> do
        s1 <- executePhase logger state PhaseGlobalStructural
        s2 <- executePhase logger s1 PhaseArrayUsage
        s3 <- executePhase logger s2 PhaseNullability
        logger "Phase: Constraint Generation..."
        start <- getCurrentTime
        let ts = garTypeSystem $ fromJust $ hsGlobalStruct s3
            aur = fromJust $ hsArrayUsage s3
            nr = fromJust $ hsNullability s3
            res = runConstraintGeneration ts aur nr (hsProgram s3)
        _ <- evaluate (Map.size (cgrConstraints res))
        end <- getCurrentTime
        logger $ printf " (%.3fs)\n" (realToFrac (diffUTCTime end start) :: Double)
        return s3 { hsConstraintGen = Just res }

    PhaseSolving | isJust (hsOrderedResult state) -> return state
    PhaseSolving -> do
        s1 <- executePhase logger state PhaseConstraintGen
        s2 <- executePhase logger s1 PhaseCallGraph
        s3 <- executePhase logger s2 PhaseArrayUsage
        s4 <- executePhase logger s3 PhaseInvariants
        logger "Phase: Constraint Solving (Ordered)..."
        start <- getCurrentTime
        let ts = garTypeSystem $ fromJust $ hsGlobalStruct s4
            aur = fromJust $ hsArrayUsage s4
            cgr = fromJust $ hsConstraintGen s4
            ir = fromJust $ hsInvariants s4
            sccs = cgrSccs $ fromJust $ hsCallGraph s4
            res = runOrderedSolver ts aur ir sccs cgr
        _ <- evaluate (length (osrErrors res) + Map.size (osrInferredSigs res))
        end <- getCurrentTime
        logger $ printf " (%.3fs)\n" (realToFrac (diffUTCTime end start) :: Double)
        return s4 { hsOrderedResult = Just res }
