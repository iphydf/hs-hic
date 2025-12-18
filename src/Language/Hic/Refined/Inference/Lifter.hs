{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
module Language.Hic.Refined.Inference.Lifter
    ( liftImplicitPolymorphism
    ) where

import           Control.Monad.State.Strict                  (State, get,
                                                              modify)
import qualified Data.Map.Strict                             as Map
import qualified Data.Set                                    as Set
import           Data.Text                                   (Text)
import           Data.Word                                   (Word32)

import           Language.Cimple                             as C
import           Language.Hic.Refined.Inference.Substitution
import           Language.Hic.Refined.Inference.Types
import           Language.Hic.Refined.Inference.Utils
import           Language.Hic.Refined.LatticeOp
import           Language.Hic.Refined.Registry
import           Language.Hic.Refined.Types


liftImplicitPolymorphism :: Registry Word32 -> State TranslatorState (Registry Word32)
liftImplicitPolymorphism (Registry defs) = do
    -- Pass 1: Identify implicit parameters for each definition
    defsWithImplicit <- Map.traverseWithKey (\name def -> do
        dtraceM ("liftImplicitPolymorphism: processing " ++ show name)
        case def of
            StructDef l ps members -> liftImplicitDef name "struct" l ps members StructDef
            UnionDef l ps members  -> liftImplicitDef name "union" l ps members UnionDef
            _                      -> return def
        ) defs
    let reg = Registry defsWithImplicit

    -- Pass 2: Update all VNominal nodes in tsNodes to include missing parameters
    st2 <- get
    let nids = Map.keys (tsNodes st2)
    dtraceM ("liftImplicitPolymorphism: Pass 2, tsNodes size=" ++ show (length nids))
    mapM_ (\nid -> do
        st3 <- get
        case Map.lookup nid (tsNodes st3) of
            Just (AnyRigidNodeF (RObject (VNominal l params) q)) -> do
                let tid = C.lexemeText l
                let name = case tid of { TIdName n -> n; _ -> "" }
                dtraceM ("liftImplicitPolymorphism: Pass 2, checking node " ++ show nid ++ " (" ++ show name ++ ") params=" ++ show (length params))
                case Map.lookup name (regDefinitions reg) of
                    Just def -> do
                        let formalParams = case def of
                                StructDef _ ps _ -> ps
                                UnionDef _ ps _  -> ps
                                _                -> []
                        if length params < length formalParams
                        then do
                            -- Missing parameters: fill with original variables from def
                            let missing = drop (length params) formalParams
                            missingIds <- mapM (\(tid', _) -> register $ AnyRigidNodeF (RObject (VVar tid' Nothing) (Quals False False))) missing
                            let res = AnyRigidNodeF (RObject (VNominal l (params ++ missingIds)) q)
                            dtraceM ("liftImplicitPolymorphism: updated node " ++ show nid ++ " (" ++ show name ++ ") with " ++ show (length missingIds) ++ " parameters")
                            modify (addNode nid res)
                        else do
                            dtraceM ("liftImplicitPolymorphism: node " ++ show nid ++ " (" ++ show name ++ ") already has " ++ show (length params) ++ "/" ++ show (length formalParams) ++ " parameters")
                    Nothing -> do
                        dtraceM ("liftImplicitPolymorphism: node " ++ show nid ++ " has name " ++ show name ++ " not in registry")
            _ -> return ()
        ) nids
    return reg

liftImplicitDef
    :: Text
    -> String
    -> Lexeme Text
    -> [(TemplateId, Variance)]
    -> [Member Word32]
    -> (Lexeme Text -> [(TemplateId, Variance)] -> [Member Word32] -> TypeDefinition Word32)
    -> State TranslatorState (TypeDefinition Word32)
liftImplicitDef name kind l ps members mk = do
    implicitVars <- Set.unions <$> mapM (\m -> do
        vars <- collectRefinableVars (mType m)
        dtraceM ("collectRefinableVars for " ++ show name ++ "." ++ show (C.lexemeText (mName m)) ++ " (node " ++ show (mType m) ++ "): " ++ show vars)
        return vars
        ) members
    let explicitSet = Set.fromList (map fst ps)
    let extraPs = [ (v, Invariant) | v <- Set.toList implicitVars, not (v `Set.member` explicitSet) ]
    let formalParams = ps ++ extraPs
    let tids = map fst formalParams
    paramIds <- mapM (\tid -> register $ AnyRigidNodeF (RObject (VVar tid Nothing) (Quals False False))) tids
    nominalId <- register $ AnyRigidNodeF (RObject (VNominal (fmap TIdName l) paramIds) (Quals False False))
    existId <- register $ AnyRigidNodeF (RObject (VExistential tids nominalId) (Quals False False))
    modify $ \s -> s { tsExistentials = Map.insert name existId (tsExistentials s) }
    if not (null extraPs) then dtraceM ("liftImplicitPolymorphism: lifted " ++ show (map fst extraPs) ++ " for " ++ kind ++ " " ++ show name) else return ()
    return $ mk l formalParams members
