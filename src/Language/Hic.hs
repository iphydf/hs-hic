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
    , runToPhase
    , emptyState
    ) where

import           Control.Monad                                        (foldM)
import           Data.Aeson                                           (ToJSON)
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
    PhaseGlobalStructural -> run "Global Structural Analysis" $ \s ->
        s { hsGlobalStruct = Just $ runGlobalStructuralAnalysis (hsProgram s) }

    PhaseArrayUsage | isJust (hsArrayUsage state) -> return state
    PhaseArrayUsage -> do
        s1 <- executePhase logger state PhaseGlobalStructural
        run_with s1 "Array Usage Analysis" $ \s ->
            let ts = garTypeSystem $ fromJust $ hsGlobalStruct s
            in s { hsArrayUsage = Just $ runArrayUsageAnalysis ts (hsProgram s) }

    PhaseCallGraph | isJust (hsCallGraph state) -> return state
    PhaseCallGraph -> run "Call Graph Analysis" $ \s ->
        s { hsCallGraph = Just $ runCallGraphAnalysis (hsProgram s) }

    PhaseInvariants | isJust (hsInvariants state) -> return state
    PhaseInvariants -> do
        s1 <- executePhase logger state PhaseGlobalStructural
        s2 <- executePhase logger s1 PhaseCallGraph
        run_with s2 "Structural Invariant Discovery" $ \s ->
            let ts = garTypeSystem $ fromJust $ hsGlobalStruct s
                sccs = cgrSccs $ fromJust $ hsCallGraph s
            in s { hsInvariants = Just $ runInvariantAnalysis ts sccs (hsProgram s) }

    PhaseNullability | isJust (hsNullability state) -> return state
    PhaseNullability -> run "Nullability Analysis" $ \s ->
        s { hsNullability = Just $ runNullabilityAnalysis (hsProgram s) }

    PhaseConstraintGen | isJust (hsConstraintGen state) -> return state
    PhaseConstraintGen -> do
        s1 <- executePhase logger state PhaseGlobalStructural
        s2 <- executePhase logger s1 PhaseArrayUsage
        s3 <- executePhase logger s2 PhaseNullability
        run_with s3 "Constraint Generation" $ \s ->
            let ts = garTypeSystem $ fromJust $ hsGlobalStruct s
                aur = fromJust $ hsArrayUsage s
                nr = fromJust $ hsNullability s
            in s { hsConstraintGen = Just $ runConstraintGeneration ts aur nr (hsProgram s) }

    PhaseSolving | isJust (hsOrderedResult state) -> return state
    PhaseSolving -> do
        s1 <- executePhase logger state PhaseConstraintGen
        s2 <- executePhase logger s1 PhaseCallGraph
        s3 <- executePhase logger s2 PhaseArrayUsage
        s4 <- executePhase logger s3 PhaseInvariants
        run_with s4 "Constraint Solving (Ordered)" $ \s ->
            let ts = garTypeSystem $ fromJust $ hsGlobalStruct s
                aur = fromJust $ hsArrayUsage s
                cgr = fromJust $ hsConstraintGen s
                ir = fromJust $ hsInvariants s
                sccs = cgrSccs $ fromJust $ hsCallGraph s
            in s { hsOrderedResult = Just $ runOrderedSolver ts aur ir sccs cgr }

  where
    run = run_with state
    run_with st name f = do
        logger $ "Phase: " ++ name ++ "..."
        start <- getCurrentTime
        let res = f st
        -- Force WHNF to ensure trace messages and accurate timing
        case res of
            HicState {} -> do
                end <- getCurrentTime
                let duration = realToFrac (diffUTCTime end start) :: Double
                logger $ printf "  (%.3fs)" duration
                return res
