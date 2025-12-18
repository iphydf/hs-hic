{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import qualified Control.Exception                                    as E
import           Control.Monad                                        (when)
import           Data.Aeson                                           (encode)
import qualified Data.ByteString                                      as B
import qualified Data.ByteString.Lazy                                 as BL
import           Data.Fix                                             (Fix (..),
                                                                       foldFix)
import           Data.Functor.Identity                                (Identity (..),
                                                                       runIdentity)
import           Data.List                                            (find,
                                                                       intercalate,
                                                                       nub)
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
                                                                       runToPhase)
import           Language.Hic.Ast                                     (HicNode (..),
                                                                       Node,
                                                                       NodeF (..))
import           Language.Hic.Core.Errors                             (Context (..),
                                                                       ErrorInfo (..))
import           Language.Hic.Core.Pretty                             (ppErrorInfo)
import           Language.Hic.Inference.Analyze                       (nodeName)
import           Language.Hic.Inference.Program                       (Program (..),
                                                                       fromCimple,
                                                                       toCimple)
import           Language.Hic.Pretty                                  (ppNode)
import           Language.Hic.Refined.Inference                       (ProductState (..),
                                                                       RefinedResult (..),
                                                                       inferRefined)
import           Language.Hic.Refined.Pretty                          (ppAnyRefinedType)
import           Language.Hic.Refined.Registry                        (Registry (..))
import           Language.Hic.Refined.Types                           (AnyRigidNodeF (..))
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
                                                                       Pretty (..),
                                                                       defaultLayoutOptions,
                                                                       layoutPretty,
                                                                       unAnnotate,
                                                                       (<+>))
import qualified Prettyprinter.Render.Terminal                        as Terminal
import qualified Prettyprinter.Render.Text                            as TextRender
import           System.Exit                                          (ExitCode (..),
                                                                       exitFailure,
                                                                       exitSuccess)
import           System.IO                                            (hIsTerminalDevice,
                                                                       stdout)
import           System.Process                                       (callProcess)
import           Text.Groom                                           (groom)
import           Text.Printf                                          (printf)

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
        Nothing -> Left $ "Unknown solver: " ++ s

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

renderDoc :: Bool -> Doc Terminal.AnsiStyle -> IO ()
renderDoc forceColor doc = do
    isTerm <- hIsTerminalDevice stdout
    if isTerm || forceColor
        then Terminal.renderIO stdout (layoutPretty defaultLayoutOptions doc)
        else TextRender.renderIO stdout (layoutPretty defaultLayoutOptions (unAnnotate doc))

filterProgram :: Options -> Program.Program Text -> Program.Program Text
filterProgram opts prog =
    let tus = Program.toList prog
        tus' = runIdentity $ C.mapAst actions tus
    in case Program.fromList tus' of
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
        result <- CIO.parseProgram (optInputs opts)
        case result of
            Left err -> do
                putStrLn $ "Parse error: " ++ err
                exitFailure
            Right program' -> do
                let program = filterProgram opts program'
                let targetPhase = fromMaybe maxBound (optStopAfter opts)

                hicState <- runToPhase putStrLn targetPhase (emptyState program)

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

                let errors = case optSolver opts of
                        SolverOrdered -> maybe [] osrErrors (hsOrderedResult hicState)
                        SolverSimple  -> map snd (typeCheckProgram program)
                        _ -> []

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
                let hicProgram = fromCimple program
                when (targetPhase >= PhaseSolving) $ do
                    putStrLn "Global Inference..."
                    let stats = collectStats hicProgram

                    if optExemplars opts
                        then showExemplars (optColor opts) hicProgram
                        else do
                            putStrLn "Comparing round-tripped ASTs..."
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
                    let refinedResult = inferRefined ts hicProgram
                    let hasWork = not (Map.null (rrSolverStates refinedResult))
                    if not hasWork
                        then putStrLn "  No refined types to analyze."
                        else do
                            putStrLn $ "  Graph size: " ++ show (Map.size (rrSolverStates refinedResult)) ++ " nodes"
                            putStrLn $ "  Registry size: " ++ show (Map.size (regDefinitions (rrRegistry refinedResult))) ++ " types"
                            case rrSolved refinedResult of
                                Right _ -> putStrLn "  Refined check successful."
                                Left ps -> do
                                    putStrLn "  Refined check failed."

                                    let errors' = rrErrors refinedResult
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

                                        let states = rrSolverStates refinedResult
                                        let ppN i = case Map.lookup i states of
                                                Just n  -> ppAnyRefinedType ppN n
                                                Nothing -> pretty i

                                        renderDoc (optColor opts) (ppErrorInfo path ei mSnippet)
                                        putStrLn ""

                                        let nodeL = Map.lookup (psNodeL ps) states
                                        let nodeR = Map.lookup (psNodeR ps) states
                                        renderDoc (optColor opts) $ "    NodeL:" <+> maybe "Nothing" (ppAnyRefinedType ppN) nodeL
                                        putStrLn ""
                                        renderDoc (optColor opts) $ "    NodeR:" <+> maybe "Nothing" (ppAnyRefinedType ppN) nodeR
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

checkFile :: Map FilePath [C.Node (C.Lexeme Text)] -> (FilePath, [C.Node (C.Lexeme Text)]) -> IO ()
checkFile loweredMap (path, nodes) = do
    let original = map (C.removeSloc . C.elideGroups) nodes
    let roundtripped = map (C.removeSloc . C.elideGroups) (loweredMap Map.! path)

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
