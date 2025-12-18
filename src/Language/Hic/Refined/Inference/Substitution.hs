{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TupleSections       #-}
module Language.Hic.Refined.Inference.Substitution
    ( substitute
    , substitutePtrTarget
    , substituteReturnType
    , collectRefinableVars
    , refreshInstance
    , refreshSignature
    , register
    ) where

import           Control.Monad                        (zipWithM)
import           Control.Monad.State.Strict           (State, get, gets, modify)
import           Data.Hashable                        (hash)
import qualified Data.IntMap.Strict                   as IntMap
import           Data.Map.Strict                      (Map)
import qualified Data.Map.Strict                      as Map
import           Data.Maybe                           (fromMaybe)
import           Data.Set                             (Set)
import qualified Data.Set                             as Set
import           Data.Text                            (Text)
import           Data.Word                            (Word32)

import           Language.Cimple                      (Lexeme)
import           Language.Hic.Refined.Context
import           Language.Hic.Refined.Inference.Types
import           Language.Hic.Refined.Inference.Utils
import           Language.Hic.Refined.PathContext
import           Language.Hic.Refined.State
import           Language.Hic.Refined.Transition
import           Language.Hic.Refined.Types


register :: AnyRigidNodeF TemplateId Word32 -> State TranslatorState Word32
register (AnyRigidNodeF (RReference ref n o q)) = do
    st <- get
    let isTargetBot i = case Map.lookup i (tsNodes st) of
            Just (AnyRigidNodeF (RTerminal SBottom)) -> True
            _                                        -> False
    let resIsBot = case ref of
            Ptr (TargetObject i) -> isTargetBot i
            Arr e _              -> isTargetBot e
            _                    -> False
    if resIsBot then return 0 -- SBottom
    else do
        nid <- gets tsNextId
        dtraceM ("Registering ID " ++ show nid ++ ": Reference " ++ show (n, o, q) ++ " -> " ++ show ref)
        modify $ \s -> (addNode nid (AnyRigidNodeF (RReference ref n o q)) s) { tsNextId = nid + 1 }
        return nid
register node = do
    nid <- gets tsNextId
    dtraceM ("Registering ID " ++ show nid ++ ": " ++ show node)
    modify $ \s -> (addNode nid node s) { tsNextId = nid + 1 }
    return nid

substitute :: (TemplateId -> State TranslatorState (Maybe Word32)) -> Word32 -> State TranslatorState Word32
substitute lookupFunc nid = do
    st <- get
    case Map.lookup nid (tsSubstCache st) of
        Just res -> return res
        Nothing -> do
            -- Pre-insert the original ID to terminate recursion.
            -- If we find it again, we haven't finished substituting it yet,
            -- but returning the ID itself is safe as it represents a fixed point
            -- for Equi-recursive types when no substitution is triggered deeper.
            modify $ \s -> s { tsSubstCache = Map.insert nid nid (tsSubstCache s) }

            res <- case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RObject s q)) -> do
                    mSubst <- case s of
                        VVar tid _idx | isParameter tid || isRefinable tid -> lookupFunc tid
                        _                                                  -> return Nothing
                    case mSubst of
                        Just actualId -> do
                            dtraceM ("substitute: " ++ show nid ++ " -> " ++ show actualId)
                            return actualId
                        Nothing -> do
                            newS <- case s of
                                VNominal name params -> VNominal name <$> mapM (substitute lookupFunc) params
                                VExistential tids body -> VExistential tids <$> substitute lookupFunc body
                                VVariant m -> VVariant <$> mapM (substitute lookupFunc) m
                                VProperty a pk -> VProperty <$> substitute lookupFunc a <*> pure pk
                                VSizeExpr ts -> VSizeExpr <$> mapM (\(a, c) -> (, c) <$> substitute lookupFunc a) ts
                                _ -> return s
                            if s == newS then return nid
                            else register $ AnyRigidNodeF (RObject newS q)

                Just (AnyRigidNodeF (RReference ref n o q)) -> do
                    newRef <- case ref of
                        Ptr target -> Ptr <$> substitutePtrTarget lookupFunc target
                        Arr e dims -> Arr <$> substitute lookupFunc e <*> mapM (substitute lookupFunc) dims
                    if ref == newRef then return nid
                    else register $ AnyRigidNodeF (RReference newRef n o q)

                Just (AnyRigidNodeF (RFunction args ret)) -> do
                    newArgs <- mapM (substitute lookupFunc) args
                    newRet <- substituteReturnType lookupFunc ret
                    if args == newArgs && ret == newRet then return nid
                    else register $ AnyRigidNodeF (RFunction newArgs newRet)

                _ -> return nid

            modify $ \s -> s { tsSubstCache = Map.insert nid res (tsSubstCache s) }
            return res

substitutePtrTarget :: (TemplateId -> State TranslatorState (Maybe Word32)) -> PtrTarget TemplateId Word32 -> State TranslatorState (PtrTarget TemplateId Word32)
substitutePtrTarget lookupFunc target = case target of
    TargetObject o -> TargetObject <$> substitute lookupFunc o
    TargetFunction args ret -> TargetFunction <$> mapM (substitute lookupFunc) args <*> substituteReturnType lookupFunc ret
    TargetOpaque tid | isRefinable tid -> do
        res <- lookupFunc tid
        case res of
            Just actualId -> do
                st <- get
                case Map.lookup actualId (tsNodes st) of
                    Just (AnyRigidNodeF (RObject (VVar tid' _) _)) -> return $ TargetOpaque tid'
                    _ -> return $ TargetObject actualId
            Nothing -> return target
    _ -> return target

substituteReturnType :: (TemplateId -> State TranslatorState (Maybe Word32)) -> ReturnType Word32 -> State TranslatorState (ReturnType Word32)
substituteReturnType lookupFunc = \case
    RetVal v -> RetVal <$> substitute lookupFunc v
    RetVoid -> return RetVoid

collectRefinableVars :: Word32 -> State TranslatorState (Set TemplateId)
collectRefinableVars nid = do
    modify $ \s -> s { tsSubstCache = Map.empty }
    -- Clear substitution cache to avoid stale results. Visited nodes are tracked via local state.
    collectRefinableVars' Set.empty nid

collectRefinableVars' :: Set Word32 -> Word32 -> State TranslatorState (Set TemplateId)
collectRefinableVars' visited nid
    | nid `Set.member` visited = return Set.empty
    | otherwise = do
        st <- get
        case Map.lookup nid (tsNodes st) of
            Just (AnyRigidNodeF n) -> foldMapVar (Set.insert nid visited) n
            Nothing                -> return Set.empty
  where
    foldMapVar :: Set Word32 -> RigidNodeF k TemplateId Word32 -> State TranslatorState (Set TemplateId)
    foldMapVar vset = \case
        RObject s _ -> case s of
            VVar tid _ | isParameter tid -> return $ Set.singleton tid
            VNominal _ ps -> Set.unions <$> mapM (collectRefinableVars' vset) ps
            VExistential tids body -> do
                vars <- collectRefinableVars' vset body
                return $ vars `Set.difference` Set.fromList tids
            VVariant m -> Set.unions <$> mapM (collectRefinableVars' vset) (IntMap.elems m)
            VProperty a _ -> collectRefinableVars' vset a
            VSizeExpr ts -> Set.unions <$> mapM (collectRefinableVars' vset . fst) ts
            _ -> return Set.empty
        RReference r _ _ _ -> case r of
            Ptr t -> case t of
                TargetObject o -> collectRefinableVars' vset o
                TargetFunction args ret -> do
                    as <- mapM (collectRefinableVars' vset) args
                    rs <- case ret of { RetVal v -> collectRefinableVars' vset v; RetVoid -> return Set.empty }
                    return $ Set.unions (rs:as)
                TargetOpaque tid | isRefinable tid -> return $ Set.singleton tid
                _ -> return Set.empty
            Arr e dims -> do
                es <- collectRefinableVars' vset e
                ds <- mapM (collectRefinableVars' vset) dims
                return $ Set.unions (es:ds)
        RFunction args ret -> do
            as <- mapM (collectRefinableVars' vset) args
            rs <- case ret of { RetVal v -> collectRefinableVars' vset v; RetVoid -> return Set.empty }
            return $ Set.unions (rs:as)
        RTerminal _ -> return Set.empty

refreshVars :: (Word32 -> Word32 -> TemplateId) -> [TemplateId] -> State TranslatorState (Map TemplateId Word32)
refreshVars mkTid vars = do
    st <- get
    let nextId = tsNextId st
    Map.fromList <$> zipWithM (\i tid -> do
        nodeId <- register $ AnyRigidNodeF (RObject (VVar (mkTid nextId (fromIntegral i)) Nothing) (Quals False False))
        return (tid, nodeId)
        ) [0..length vars - 1] vars

refreshInstance :: Maybe (Lexeme Text) -> Word32 -> State TranslatorState Word32
refreshInstance loc nid = do
    vars <- collectRefinableVars nid
    nid' <- if Set.null vars then return nid
    else do
        let varList = Set.toList vars
        freshMap <- refreshVars (\nextId i -> TIdInstance (toInteger (nextId + i))) varList

        modify $ \s -> s { tsSubstCache = Map.empty }
        let lookupFunc tid = return $ Map.lookup tid freshMap
        substitute lookupFunc nid

    st' <- get
    case Map.lookup nid' (tsNodes st') of
        Just (AnyRigidNodeF (RTerminal _)) -> return nid'
        _ -> do
            freshId <- gets tsNextId
            modify $ \s -> s { tsNextId = freshId + 1 }
            let tid = TIdInstance (toInteger freshId)
            let node = AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))
            modify (addNode freshId node)
            modify (addConstraint loc (PathContext Map.empty Map.empty) freshId nid')
            return freshId


refreshSignature :: [Word32] -> ReturnType Word32 -> State TranslatorState ([Word32], ReturnType Word32, Map Word32 Word32)
refreshSignature params ret = do
    let allIds = params ++ case ret of { RetVal v -> [v]; RetVoid -> [] }
    vars <- Set.unions <$> mapM collectRefinableVars allIds
    dtraceM ("refreshSignature: allIds=" ++ show allIds ++ ", refinableVars=" ++ show vars)
    if Set.null vars then return (params, ret, Map.empty)
    else do
        st <- get
        let varList = Set.toList vars
        let varToNode = Map.fromList [ (tid, nid) | (nid, AnyRigidNodeF (RObject (VVar tid _) _)) <- Map.toList (tsNodes st), tid `Set.member` vars ]

        let h = fromIntegral (hash allIds)
        freshMap <- refreshVars (\nextId i -> TIdSkolem h h (nextId + i)) varList

        modify $ \s -> s { tsSubstCache = Map.empty }
        let lookupFunc tid = return $ Map.lookup tid freshMap
        params' <- mapM (substitute lookupFunc) params
        ret' <- substituteReturnType lookupFunc ret

        let nodeMapping = Map.fromList [ (origId, freshId) | (tid, freshId) <- Map.toList freshMap, Just origId <- [Map.lookup tid varToNode] ]
        dtraceM ("refreshSignature: nodeMapping=" ++ show nodeMapping)

        return (params', ret', nodeMapping)
