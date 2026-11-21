{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import qualified Control.Exception                                    as E
import           Control.Monad                                        (foldM,
                                                                       when)
import           Data.Aeson                                           (encode)
import qualified Data.ByteString                                      as B
import qualified Data.ByteString.Lazy                                 as BL
import           Data.Fix                                             (Fix (..),
                                                                       foldFix)
import           Data.Functor.Identity                                (Identity (..),
                                                                       runIdentity)
import           Data.List                                            (find,
                                                                       intercalate,
                                                                       isSuffixOf,
                                                                       nub,
                                                                       sortOn)
import           Data.Map.Strict                                      (Map)
import qualified Data.Map.Strict                                      as Map
import           Data.Maybe                                           (fromMaybe,
                                                                       mapMaybe)
import           Data.Set                                             (Set)
import qualified Data.Set                                             as Set
import           Data.Text                                            (Text)
import qualified Data.Text                                            as T
import qualified Data.Text.Encoding                                   as T
import qualified Data.Text.Encoding.Error                             as T
import qualified Data.Text.IO                                         as Text
import           Data.Time.Clock                                      (diffUTCTime,
                                                                       getCurrentTime)
import qualified Language.Cimple                                      as C
import qualified Language.Cimple.IO                                   as CIO
import qualified Language.Cimple.Program                              as Program
import           Language.Hic                                         (HicState (..),
                                                                       Phase (..),
                                                                       emptyState,
                                                                       executePhase,
                                                                       runToPhase)
import           Language.Hic.Ast                                     (HicNode (..),
                                                                       Node,
                                                                       NodeF (..))
import           Language.Hic.Core.Errors                             (Context (..),
                                                                       ErrorInfo (..),
                                                                       TypeError (..))
import           Language.Hic.Core.Pretty                             (ppErrorInfo)
import           Language.Hic.Inference.Analyze                       (nodeName)
import           Language.Hic.Inference.Program                       (Program (..),
                                                                       fromCimple,
                                                                       fromCimpleWith,
                                                                       toCimple)
import           Language.Hic.Pretty                                  (ppNode)
import           Language.Hic.Refined.Inference                       (RefinedResult (..),
                                                                       collectRefined,
                                                                       collectedSize,
                                                                       solveCollected)
import           Language.Hic.Refined.Registry                        (Registry (..),
                                                                       TypeDefinition (..))
import           Language.Hic.TypeSystem.Ordered.ArrayUsage           (runArrayUsageAnalysis)
import           Language.Hic.TypeSystem.Ordered.Base                 (OrderedSolverResult (..),
                                                                       runOrderedSolver)
import           Language.Hic.TypeSystem.Ordered.CallGraph            (CallGraphResult (..),
                                                                       runCallGraphAnalysis)
import           Language.Hic.TypeSystem.Ordered.ConstraintGeneration (ConstraintGenResult (..),
                                                                       runConstraintGeneration)
import qualified Language.Hic.TypeSystem.Ordered.ConstraintGeneration as CG
import           Language.Hic.TypeSystem.Ordered.HotspotAnalysis      (GlobalAnalysisResult (..),
                                                                       runGlobalStructuralAnalysis)
import           Language.Hic.TypeSystem.Ordered.Nullability          (runNullabilityAnalysis)
import           Language.Hic.TypeSystem.Standard.Base                (typeCheckProgram)
import qualified Language.Hic.TypeSystem.Standard.Constraints         as TC
import           Language.Hic.TypeSystem.Standard.Solver              (solveConstraints)
import           Options.Applicative
import           Prettyprinter                                        (Doc,
                                                                       defaultLayoutOptions,
                                                                       layoutPretty,
                                                                       unAnnotate)
import qualified Prettyprinter.Render.Terminal                        as Terminal
import qualified Prettyprinter.Render.Text                            as TextRender
import           System.Exit                                          (ExitCode (..),
                                                                       exitFailure,
                                                                       exitSuccess)
import           System.IO                                            (hFlush,
                                                                       hIsTerminalDevice,
                                                                       stdout)
import           System.Process                                       (callProcess)
import           Text.Groom                                           (groom)
import           Text.Printf                                          (printf)

runTimed :: String -> IO a -> IO a
runTimed name phase = do
    putStr $ "Phase: " ++ name ++ "..."
    hFlush stdout
    start <- getCurrentTime
    res <- phase
    end <- getCurrentTime
    let duration = realToFrac (diffUTCTime end start) :: Double
    printf " (%.3fs)\n" duration
    return res

parsePhase :: String -> Either String Phase
parsePhase s =
    case find (\p -> phaseToText p == T.pack s) [minBound .. maxBound] of
        Just p  -> Right p
        Nothing -> Left $ "Unknown phase: " ++ s

phaseToText :: Phase -> Text
phaseToText = \case
    PhaseGlobalStructural -> "global-structural"
    PhaseArrayUsage       -> "array-usage"
    PhaseCallGraph        -> "call-graph"
    PhaseInvariants       -> "structural-invariants"
    PhaseNullability      -> "nullability"
    PhaseConstraintGen    -> "constraint-gen"
    PhaseSolving          -> "solving"

data SolverType = SolverOrdered | SolverSimple | SolverRefined
    deriving (Show, Eq, Ord, Enum, Bounded)

solverName :: SolverType -> String
solverName = \case
    SolverOrdered -> "ordered"
    SolverSimple  -> "simple"
    SolverRefined -> "refined"

parseSolver :: String -> Either String SolverType
parseSolver s =
    case find (\(p) -> solverName p == s) [minBound .. maxBound] of
        Just p  -> Right p
        Nothing -> Left $ "Unknown solver: " ++ s ++ " (available: " ++ intercalate ", " (map solverName [minBound .. maxBound]) ++ ")"

data Options = Options
    { optInputs     :: [FilePath]
    , optExemplars  :: Bool
    , optDumpJson   :: Maybe FilePath
    , optStopAfter  :: Maybe Phase
    , optMaxErrors  :: Int
    , optSolver     :: SolverType
    , optNoOwner    :: Bool
    , optNoNullable :: Bool
    , optColor      :: Bool
    , optCostReport :: Int
    , optAllowCasts :: [FilePath]
    }

options :: Parser Options
options = Options
    <$> some (strArgument (metavar "FILE..." <> help "Input C files"))
    <*> switch (long "exemplars" <> help "Show exemplars of inferred structures")
    <*> optional (strOption (long "dump-json" <> metavar "BASENAME" <> help "Dump analysis results for each phase to BASENAME-<phase>.json"))
    <*> optional (option (eitherReader parsePhase)
        (  long "stop-after"
        <> metavar "PHASE"
        <> help ("Stop after a specific phase (" ++ intercalate ", " (map (T.unpack . phaseToText) [minBound .. maxBound]) ++ ")")
        ))
    <*> option auto
        (  long "max-errors"
        <> metavar "COUNT"
        <> value 5
        <> showDefault
        <> help "Maximum number of errors to display"
        )
    <*> option (eitherReader parseSolver)
        (  long "solver"
        <> metavar "SOLVER"
        <> value SolverRefined
        <> showDefault
        <> help "Solver to use (ordered, simple, refined)"
        )
    <*> switch (long "no-owner" <> help "Disable owner checks")
    <*> switch (long "no-nullable" <> help "Disable nullable/nonnull checks")
    <*> switch (long "color" <> help "Always output color diagnostics")
    <*> option auto
        (  long "cost-report"
        <> metavar "COUNT"
        <> value 0
        <> help "Show the COUNT functions that make the most type nodes and solver steps"
        )
    <*> many (strOption
        (  long "allow-casts"
        <> metavar "FILE"
        <> help "Don't report casts between incompatible types in FILE (e.g. OS glue code)"
        ))

-- | The functions whose analysis costs the most: type nodes made while
-- collecting them, and solver steps for their constraints.
costReport :: Int -> RefinedResult -> IO ()
costReport n res = do
    let functionOf (Just file) line = case Map.lookupLE line =<< Map.lookup file (rrFunctionStarts res) of
            Just (_, name) -> (file, name)
            Nothing        -> (file, "<top level>")
        functionOf Nothing _ = ("<unknown>", "<unknown>")
        steps = Map.fromListWith (+) [ (functionOf file line, k) | ((file, line), k) <- Map.toList (rrStepsByOrigin res) ]
        top m = take n $ sortOn (negate . snd) $ Map.toList m
        printRow ((file, name), k) = printf "    %9d  %s (%s)\n" k (T.unpack name) (reverse (takeWhile (/= '/') (reverse file)))
    putStrLn $ "  Type nodes by function (top " ++ show n ++ "):"
    mapM_ printRow (top (rrNodesByFunction res))
    putStrLn $ "  Solver steps by function (top " ++ show n ++ "):"
    mapM_ printRow (top steps)
    -- Each void * a struct holds, directly or in structs it holds by value,
    -- is a type parameter, and every use of the struct carries all of them.
    let params = [ (C.lexemeText l, length ps) | (_, StructDef l ps _) <- Map.toList (regDefinitions (rrRegistry res)) ]
    putStrLn $ "  Structs with the most type parameters (top " ++ show n ++ "):"
    mapM_ (\(name, k) -> printf "    %9d  %s\n" k (T.unpack name)) (take n (sortOn (negate . snd) params))

renderDoc :: Bool -> Doc Terminal.AnsiStyle -> IO ()
renderDoc forceColor doc = do
    isTerm <- hIsTerminalDevice stdout
    if isTerm || forceColor
        then Terminal.renderIO stdout (layoutPretty defaultLayoutOptions doc)
        else TextRender.renderIO stdout (layoutPretty defaultLayoutOptions (unAnnotate doc))

-- | The program without the annotations the options say to leave out: as
-- it is if they leave none out.
filterProgram :: Options -> Program.Program Text -> Program.Program Text
filterProgram opts prog
    | not (optNoOwner opts || optNoNullable opts) = prog
    | otherwise = case Program.fromList (runIdentity (C.mapAst actions (Program.toList prog))) of
        Left err -> error $ "filterProgram: " ++ err
        Right p  -> p
  where
    actions :: C.IdentityActions Identity Text
    actions = C.identityActions
        { C.doNode = \_ _ next -> do
            n <- next
            case unFix n of
                C.TyOwner i | optNoOwner opts -> return i
                C.TyNonnull i | optNoNullable opts -> return i
                C.TyNullable i | optNoNullable opts -> return i
                C.NonNullParam i | optNoNullable opts -> return i
                C.NullableParam i | optNoNullable opts -> return i
                C.DeclSpecArray _ size | optNoNullable opts -> return $ Fix $ C.DeclSpecArray C.NullabilityUnspecified size
                _ -> return n
        }

main :: IO ()
main = do
    totalStart <- getCurrentTime
    let printTotalTime = do
            totalEnd <- getCurrentTime
            let totalDuration = realToFrac (diffUTCTime totalEnd totalStart) :: Double
            printf "\nTotal time: %.3fs\n" totalDuration

    E.handle handler $ E.finally (do
        opts <- execParser (info (options <**> helper) fullDesc)
        result <- runTimed "Parsing" $ CIO.parseProgram (optInputs opts)
        case result of
            Left err -> do
                putStrLn $ "Parse error: " ++ err
                exitFailure
            Right program' -> do
                let program = filterProgram opts program'
                let targetPhase = fromMaybe maxBound (optStopAfter opts)

                let runPhaseLogger msg = do
                        putStr msg
                        hFlush stdout

                let phasesToRun = case optStopAfter opts of
                        Just p  -> [minBound .. p]
                        Nothing -> case optSolver opts of
                            SolverOrdered -> [minBound .. maxBound]
                            SolverSimple  -> []
                            SolverRefined -> [PhaseGlobalStructural]

                hicState <- foldM (executePhase runPhaseLogger) (emptyState program) phasesToRun

                let dump p res = case optDumpJson opts of
                        Just base -> do
                            let path = base ++ "-" ++ T.unpack (phaseToText p) ++ ".json"
                            BL.writeFile path (encode res)
                        Nothing -> return ()

                dump PhaseGlobalStructural (hsGlobalStruct hicState)
                dump PhaseArrayUsage (hsArrayUsage hicState)
                dump PhaseCallGraph (hsCallGraph hicState)
                dump PhaseInvariants (hsInvariants hicState)
                dump PhaseNullability (hsNullability hicState)
                dump PhaseConstraintGen (hsConstraintGen hicState)
                dump PhaseSolving (hsOrderedResult hicState)

                errors <- case optSolver opts of
                    SolverOrdered -> return $ maybe [] osrErrors (hsOrderedResult hicState)
                    SolverSimple  -> runTimed "Standard Type Checking" $ E.evaluate $ map snd (typeCheckProgram program)
                    _ -> return []

                let extractPath ei = case find isFile (errContext ei) of
                        Just (InFile p) -> p
                        _               -> "unknown"
                    isFile = \case InFile _ -> True; _ -> False

                if null errors
                    then putStrLn "Type check successful."
                    else do
                        putStrLn "Type check failed with the following errors:"
                        let paths = nub $ map extractPath errors
                        fileCache <- Map.fromList <$> mapM (\p -> do
                            if p == "unknown"
                                then return (p, [])
                                else do
                                    content <- T.decodeUtf8With T.lenientDecode <$> B.readFile p
                                    return (p, T.lines content)) paths

                        mapM_ (\ei -> do
                            let path = extractPath ei
                            let mSnippet = case errLoc ei of
                                    Just (C.L (C.AlexPn _ lineNum _) _ _) -> do
                                        ls <- Map.lookup path fileCache
                                        if lineNum > 0 && lineNum <= length ls
                                            then Just (ls !! (lineNum - 1))
                                            else Nothing
                                    Nothing -> Nothing
                            renderDoc (optColor opts) (ppErrorInfo path ei mSnippet)
                            putStrLn "") (take (optMaxErrors opts) errors)
                        when (length errors > optMaxErrors opts) $
                            putStrLn $ "... and " ++ show (length errors - optMaxErrors opts) ++ " more errors elided."

                -- Hic Inference
                -- The type system the global analysis worked out is the
                -- program's, so inference needn't work it out again.
                hicProgram <- runTimed "Global Inference" $ E.evaluate $
                    maybe fromCimple (fromCimpleWith . garTypeSystem) (hsGlobalStruct hicState) program
                when (targetPhase >= PhaseSolving) $ do
                    let stats = collectStats hicProgram

                    if optExemplars opts
                        then showExemplars (optColor opts) hicProgram
                        else do
                            runTimed "AST Round-tripping" $ do
                                let loweredProgram = toCimple hicProgram
                                let originalList = Program.toList program
                                let loweredMap = Map.fromList $ Program.toList loweredProgram

                                mapM_ (checkFile loweredMap) originalList

                            putStrLn "\nDiagnostics:"
                            if null (progDiagnostics hicProgram)
                                then putStrLn "  None."
                                else mapM_ (Text.putStrLn . ("  " <>)) (progDiagnostics hicProgram)

                            putStrLn "\nInferred Constructs Statistics:"
                            if Map.null stats
                                then putStrLn $ "  No high-level constructs inferred (baseline only)."
                                else mapM_ (\(name, count) -> putStrLn $ "  " ++ name ++ ": " ++ show count) (Map.toList stats)

                -- Refined Solver
                when (optSolver opts == SolverRefined && targetPhase >= PhaseSolving) $ do
                    putStrLn "Refined Type Analysis..."
                    let ts = maybe Map.empty (garTypeSystem) (hsGlobalStruct hicState)
                    collected <- runTimed "Refined Constraint Collection" $ E.evaluate $ collectRefined ts hicProgram
                    let graphSize = collectedSize collected
                    putStrLn $ "  Graph size: " ++ show graphSize ++ " nodes"
                    refinedResult <- runTimed "Refined Solving" $ E.evaluate $ solveCollected hicProgram collected
                    let hasWork = graphSize /= 0
                    if not hasWork
                        then putStrLn "  No refined types to analyze."
                        else do
                            putStrLn $ "  Solver steps: " ++ show (rrSolverSteps refinedResult)
                            when (optCostReport opts > 0) $ costReport (optCostReport opts) refinedResult
                            putStrLn $ "  Registry size: " ++ show (Map.size (regDefinitions (rrRegistry refinedResult))) ++ " types"
                            -- The errors are the solver's conflicts and what
                            -- collecting the constraints found, but casts in
                            -- the files allowed them.
                            let allowedCast ei = case errType ei of
                                    RefinedCastMismatch -> any (`isFileSuffix` extractPath ei) (optAllowCasts opts)
                                    _                   -> False
                                isFileSuffix file path = path == file || ('/' : file) `isSuffixOf` path
                            case filter (not . allowedCast) (rrErrors refinedResult) of
                                [] -> putStrLn "  Refined check successful."
                                errors' -> do
                                    putStrLn "  Refined check failed."

                                    let paths' = nub $ map extractPath errors'
                                    fileCache' <- Map.fromList <$> mapM (\p -> do
                                        if p == "unknown"
                                            then return (p, [])
                                            else do
                                                content <- E.catch (T.decodeUtf8With T.lenientDecode <$> B.readFile p)
                                                                   (\(_ :: E.IOException) -> return "")
                                                return (p, T.lines content)) paths'

                                    mapM_ (\ei -> do
                                        let path = extractPath ei
                                        let mSnippet = case errLoc ei of
                                                Just (C.L (C.AlexPn _ lineNum _) _ _) -> do
                                                    ls <- Map.lookup path fileCache'
                                                    if lineNum > 0 && lineNum <= length ls
                                                        then Just (ls !! (lineNum - 1))
                                                        else Nothing
                                                Nothing -> Nothing

                                        renderDoc (optColor opts) (ppErrorInfo path ei mSnippet)
                                        putStrLn "") (take (optMaxErrors opts) errors')

                                    exitFailure

                return ()

        ) printTotalTime
  where
    handler :: E.SomeException -> IO ()
    handler e = case E.fromException e of
        Just ec -> E.throwIO (ec :: ExitCode)
        Nothing -> do
            putStr . unlines . take 20 . map (take 200) . lines $ show e
            exitFailure

showExemplars :: Bool -> Program (C.Lexeme Text) -> IO ()
showExemplars forceColor Program{..} = do
    let exemplars :: Map String (Text, Node (C.Lexeme Text))
        exemplars = Map.fromListWith (\_ old -> old) $
            [ (name, (C.sloc path n, n))
            | (path, nodes) <- Map.toList progAsts
            , node <- nodes
            , (name, n) <- collectExemplars node
            ]
    mapM_ printExemplar (Map.toList exemplars)
  where
    collectExemplars :: Node (C.Lexeme Text) -> [(String, Node (C.Lexeme Text))]
    collectExemplars n@(Fix (HicNode h)) = (nodeName h, n) : concatMap collectExemplars h
    collectExemplars (Fix (CimpleNode f)) = concatMap collectExemplars f

    printExemplar (name, (loc, node)) = do
        putStrLn $ "Exemplar for " ++ name ++ " at " ++ T.unpack loc ++ ":"
        renderDoc forceColor (ppNode node)
        putStrLn "\n"

collectStats :: Program (C.Lexeme Text) -> Map String Int
collectStats Program{..} =
    Map.unionsWith (+) . map (Map.unionsWith (+) . map countNode) $ Map.elems progAsts

countNode :: Node (C.Lexeme Text) -> Map String Int
countNode = foldFix $ \case
    CimpleNode f -> Map.unionsWith (+) f
    HicNode h    -> Map.insertWith (+) (nodeName h) 1 (Map.unionsWith (+) h)

-- | Nodes as the round trip compares them: without where they are, and with
-- the nodes of groups in place of the groups (what 'C.removeSloc' and
-- 'C.elideGroups' do, in one walk).
comparable :: [C.Node (C.Lexeme Text)] -> [C.Node (C.Lexeme Text)]
comparable = map (runIdentity . C.mapAst actions)
  where
    actions :: C.IdentityActions Identity Text
    actions = C.identityActions
        { C.doLexeme = \_ (C.L _ c t) _ -> pure (C.L (C.AlexPn 0 0 0) c t)
        , C.doNodes = \_ _ next -> concatMap flatten <$> next
        }
    flatten (Fix (C.Group ns)) = concatMap flatten ns
    flatten n                  = [n]

checkFile :: Map FilePath [C.Node (C.Lexeme Text)] -> (FilePath, [C.Node (C.Lexeme Text)]) -> IO ()
checkFile loweredMap (path, nodes) = do
    let original = comparable nodes
    let roundtripped = comparable (loweredMap Map.! path)

    if original == roundtripped
        then return ()
        else do
            putStrLn $ "  Round-trip failed for " ++ path
            let origFile = "/tmp/hic-check-original.ast"
            let newFile = "/tmp/hic-check-roundtripped.ast"
            writeFile origFile (groom original)
            writeFile newFile (groom roundtripped)
            putStrLn "Diff:"
            callProcess "diff" ["-u", "--color=auto", origFile, newFile]
            exitFailure
