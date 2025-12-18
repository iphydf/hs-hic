{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Core.ErrorMessageSpec (spec) where

import qualified Data.Map.Strict                                      as Map
import           Data.Text                                            (Text)
import qualified Data.Text                                            as T
import           GHC.Stack                                            (HasCallStack)
import           Language.Hic.Core.Errors                             (ErrorInfo (..))
import           Language.Hic.Core.Pretty                             (ppErrorInfo,
                                                                       renderPlain)
import           Language.Hic.Inference.EngineSpec                    (mustParse)
import qualified Language.Hic.TypeSystem.Core.Base                    as TS
import           Language.Hic.TypeSystem.Ordered.ArrayUsage           (runArrayUsageAnalysis)
import           Language.Hic.TypeSystem.Ordered.Base                 (OrderedSolverResult (..),
                                                                       runOrderedSolver)
import           Language.Hic.TypeSystem.Ordered.CallGraph            (CallGraphResult (..),
                                                                       runCallGraphAnalysis)
import           Language.Hic.TypeSystem.Ordered.ConstraintGeneration (runConstraintGeneration)
import           Language.Hic.TypeSystem.Ordered.HotspotAnalysis      (GlobalAnalysisResult (..),
                                                                       runGlobalStructuralAnalysis)
import           Language.Hic.TypeSystem.Ordered.Invariants           (runInvariantAnalysis)
import           Language.Hic.TypeSystem.Ordered.Nullability          (runNullabilityAnalysis)
import           Test.Hspec

spec :: Spec

spec = do
    it "reproducibility of the toxcore memory error" $ do
        prog <- mustParse
            [ "typedef void tox_memory_dealloc_cb(void *_Nonnull self, void *_Owned _Nullable ptr);"
            , "struct Tox_Memory_Funcs {"
            , "    tox_memory_dealloc_cb *_Nonnull dealloc_callback;"
            , "};"
            , "struct Tox_Memory {"
            , "    const struct Tox_Memory_Funcs *_Nonnull funcs;"
            , "    void *_Nullable user_data;"
            , "};"
            , "void tox_memory_dealloc(const struct Tox_Memory *_Nonnull mem, void *_Owned _Nullable ptr)"
            , "{"
            , "    mem->funcs->dealloc_callback(mem->user_data, ptr);"
            , "}"
            , "void tox_memory_free(struct Tox_Memory *_Nullable mem)"
            , "{"
            , "    if (mem == nullptr) {"
            , "        return;"
            , "    }"
            , "    tox_memory_dealloc(mem, mem);"
            , "}"
            ]
        let gar = runGlobalStructuralAnalysis prog
            ts = garTypeSystem gar
            cgr = runCallGraphAnalysis prog
            aua = runArrayUsageAnalysis ts prog
            na = runNullabilityAnalysis prog
            ir = runInvariantAnalysis ts (cgrSccs cgr) prog
            cg = runConstraintGeneration ts aua na prog
            osr = runOrderedSolver ts aua ir (cgrSccs cgr) cg
            errors = osrErrors osr
        length errors `shouldSatisfy` (> 0)
