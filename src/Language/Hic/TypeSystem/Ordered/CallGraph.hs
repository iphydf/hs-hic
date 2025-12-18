{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Ordered.CallGraph
    ( CallGraphResult (..)
    , CallGraph
    , SccType (..)
    , runCallGraphAnalysis
    ) where

import           Control.Monad.State.Strict (State, execState)
import qualified Control.Monad.State.Strict as State
import           Data.Aeson                 (ToJSON)
import           Data.Fix                   (Fix (..), foldFix)
import           Data.Graph                 (SCC (..), stronglyConnComp)
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import           GHC.Generics               (Generic)
import           Language.Cimple            (Lexeme (..), Node, NodeF (..))
import qualified Language.Cimple            as C
import qualified Language.Cimple.Program    as Program

type CallGraph = Map Text (Set Text)

data SccType = Acyclic Text | Cyclic [Text]
    deriving (Show, Eq, Generic)

instance ToJSON SccType

data CallGraphResult = CallGraphResult
    { cgrDirectCalls :: CallGraph
    , cgrSccs        :: [SccType]
    } deriving (Show, Generic)

instance ToJSON CallGraphResult

data AnalysisState = AnalysisState
    { asCurrentFunc :: Maybe Text
    , asCalls       :: CallGraph
    , asLocalVars   :: Set Text
    }

runCallGraphAnalysis :: Program.Program Text -> CallGraphResult
runCallGraphAnalysis program =
    let initialState = AnalysisState Nothing Map.empty Set.empty
        finalState = execState (mapM_ (mapM_ traverseNode . snd) (Program.toList program)) initialState
        calls = asCalls finalState
        -- Convert Map to adjacency list for Data.Graph.stronglyConnComp
        -- Triple: (node_value, key, [callees])
        adjacencyList = [ (name, name, Set.toList callees) | (name, callees) <- Map.toList calls ]
        sccs = map fromSCC $ stronglyConnComp adjacencyList
    in CallGraphResult calls sccs
  where
    fromSCC (AcyclicSCC node) = Acyclic node
    fromSCC (CyclicSCC nodes) = Cyclic nodes

    traverseNode = snd . foldFix alg
      where
        alg f = (Fix (fmap fst f), case f of
            C.FunctionDefn _ (protoOrig, _) (_, bodyAction) -> do
                case unFix protoOrig of
                    C.FunctionPrototype _ (L _ _ name) params -> do
                        oldFunc <- State.gets asCurrentFunc
                        oldVars <- State.gets asLocalVars
                        State.modify $ \s -> s { asCurrentFunc = Just name, asLocalVars = Set.empty }
                        mapM_ registerParam params
                        -- Ensure the function exists in the map even if it calls nothing
                        State.modify $ \s -> s { asCalls = Map.insertWith Set.union name Set.empty (asCalls s) }
                        bodyAction
                        State.modify $ \s -> s { asCurrentFunc = oldFunc, asLocalVars = oldVars }
                    _ -> bodyAction

            C.VarDeclStmt (declOrig, _) mInit -> do
                case unFix declOrig of
                    C.VarDecl _ (L _ _ name) _ ->
                        State.modify $ \s -> s { asLocalVars = Set.insert name (asLocalVars s) }
                    _ -> return ()
                mapM_ snd mInit

            C.FunctionCall (funOrig, _) args -> do
                case unFix funOrig of
                    C.VarExpr (L _ _ callee) -> do
                        locals <- State.gets asLocalVars
                        mCaller <- State.gets asCurrentFunc
                        case mCaller of
                            Just caller | not (Set.member callee locals) -> State.modify $ \s ->
                                let calls = Map.insertWith Set.union caller (Set.singleton callee) (asCalls s)
                                    calls' = Map.insertWith Set.union callee Set.empty calls
                                in s { asCalls = calls' }
                            _ -> return ()
                    _ -> return ()
                mapM_ snd args

            node -> sequence_ (fmap snd node))

    registerParam = snd . foldFix alg'
      where
        alg' f = (Fix (fmap fst f), case f of
            C.VarDecl _ (L _ _ name) _ ->
                State.modify $ \s -> s { asLocalVars = Set.insert name (asLocalVars s) }
            C.NonNullParam (_, action) -> action
            C.NullableParam (_, action) -> action
            node -> sequence_ (fmap snd node))
