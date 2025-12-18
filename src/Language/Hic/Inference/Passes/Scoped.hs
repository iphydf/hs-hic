{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Inference.Passes.Scoped
    ( feature
    ) where

import           Control.Monad.State.Strict     (State)
import qualified Control.Monad.State.Strict     as State
import           Data.Fix                       (Fix (..), foldFix, foldFixM)
import           Data.Text                      (Text)
import qualified Debug.Trace                    as Debug
import qualified Language.Cimple                as C
import           Language.Hic.Ast               (CleanupAction (..),
                                                 HicNode (..), Node, NodeF (..))
import           Language.Hic.Inference.Context (Context)
import           Language.Hic.Inference.Feature (Feature (..))

debugging :: Bool
debugging = False

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

feature :: Feature
feature = Feature
    { featureName     = "Scoped"
    , featureGather   = \_ ctx -> ctx
    , featureInfer    = infer
    , featureValidate = \_ _ -> []
    , featureLower    = lower
    }

infer :: Context -> FilePath -> Node (C.Lexeme Text) -> State Bool (Node (C.Lexeme Text))
infer _ctx _file = foldFixM alg
  where
    alg (CimpleNode (C.CompoundStmt stmts)) = do
        stmts' <- inferScoped stmts
        return $ Fix $ CimpleNode $ C.CompoundStmt stmts'
    alg f = return $ Fix f

    inferScoped stmts
        | (body, [Fix (CimpleNode (C.Label l cleanup))]) <- splitAt (length stmts - 1) stmts
        , (resource : rest) <- body = do
            dtraceM $ "inferScoped: found label " ++ show l
            dtraceM $ "inferScoped: resource node " ++ show (fmap (const ()) (unFix resource))
            if isResource resource
                then do
                    dtraceM $ "inferScoped: IS resource"
                    if any (isGoto l) rest
                        then do
                            dtraceM $ "inferScoped: FOUND goto"
                            State.modify (const True)
                            let res = Fix $ HicNode $ Scoped resource (Fix $ CimpleNode $ C.Group rest) [CleanupAction (Just (Fix $ CimpleNode $ C.VarExpr l)) cleanup]
                            return [res]
                        else dtraceM "inferScoped: NO goto" >> return stmts
                else dtraceM "inferScoped: NOT resource" >> return stmts
    inferScoped stmts = return stmts

    isResource (Fix (CimpleNode (C.VarDeclStmt (Fix (CimpleNode (C.VarDecl _ _ _))) (Just _)))) = True
    isResource _ = False

    isGoto l = foldFix $ \case
        CimpleNode (C.Goto l') | C.lexemeText l == C.lexemeText l' -> True
        f -> any id f

lower :: HicNode l (C.Node l) -> Maybe (C.Node l)
lower (Scoped resource body cleanup) =
    Just $ Fix $ C.Group $ [resource, body] ++ concatMap lowerCleanup cleanup
  where
    lowerCleanup (CleanupAction (Just l) b) = [Fix $ C.Label (extractLexeme l) b]
    lowerCleanup (CleanupAction Nothing b)  = [b]

    extractLexeme (Fix (C.VarExpr l)) = l
    extractLexeme _                   = error "lowerHic: expected label name"
lower _ = Nothing
