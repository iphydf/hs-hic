{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}

module Language.Hic.TypeSystem.Ordered.InvariantsSpec (spec) where

import           Data.Bifunctor                                  (bimap)
import           Data.Fix                                        (Fix (..),
                                                                  foldFix)
import           Data.Map.Strict                                 (Map)
import qualified Data.Map.Strict                                 as Map
import           Data.Maybe                                      (fromMaybe)
import qualified Data.Set                                        as Set
import           Data.Text                                       (Text)
import qualified Language.Cimple.Program                         as Program
import           Language.Hic.Core.TypeSystem                    (FullTemplateF (..),
                                                                  Invariant (..),
                                                                  Phase (..),
                                                                  TemplateId (..),
                                                                  TypeInfoF (..),
                                                                  pattern Template)
import qualified Language.Hic.Core.TypeSystem                    as TS
import           Language.Hic.TestUtils                          (mustParse)
import           Language.Hic.TypeSystem.Core.Constraints        (Constraint (..))
import           Language.Hic.TypeSystem.Ordered.CallGraph       (cgrSccs,
                                                                  runCallGraphAnalysis)
import qualified Language.Hic.TypeSystem.Ordered.HotspotAnalysis as GSA
import           Language.Hic.TypeSystem.Ordered.Invariants
import qualified Language.Hic.TypeSystem.Ordered.Specializer     as Spec
import           Test.Hspec
import           Test.Hspec.QuickCheck                           (modifyMaxSuccess)
import           Test.QuickCheck                                 (within)

runAnalysis :: Program.Program Text -> InvariantResult
runAnalysis prog =
    let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        sccs = cgrSccs $ runCallGraphAnalysis prog
    in runInvariantAnalysis ts sccs prog

spec :: Spec
spec = do
    describe "Structural Invariant Discovery" $ do
        it "discovers structural links between specific array elements" $ do
            prog <- mustParse
                [ "struct My_Data { void *h[10]; };"
                , "void f(struct My_Data *d) {"
                , "    d->h[0] = d->h[1];"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Data" (irInvariants res)
            -- We expect an Equality invariant between Template(h, index=0) and Template(h, index=1)
            -- Note: h is an array of void*, so it will be Pointer (Template h index)
            let isIndexedEquality = \case
                    InvEquality t1 t2 ->
                        case (Spec.collectTemplates t1, Spec.collectTemplates t2) of
                            (s1, s2) | not (Set.null s1) && s1 == s2 ->
                                -- Both sides refer to the same templates, check if indices differ
                                let getIndices = foldFix $ \case
                                        TS.TemplateF (FT _ mIdx) -> fromMaybe [] mIdx
                                        TS.SingletonF _ v -> [v]
                                        f -> concat f
                                in getIndices t1 /= getIndices t2
                            _ -> False
                    _ -> False
            any isIndexedEquality invs `shouldBe` True

        it "requires more than 2 passes for deep transitive links in cycles" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "void h1(my_cb *cb, void *u) { h2(cb, u); }"
                , "void h2(my_cb *cb, void *u) { h3(cb, u); }"
                , "void h3(my_cb *cb, void *u) { h4(cb, u); }"
                , "void h4(my_cb *cb, void *u) { cb(u); h1(cb, u); }" -- Cycle
                ]
            let res = runAnalysis prog
            let links = Map.findWithDefault [] "h1" (irFunctionLinks res)
            any (\case { InvCallable {} -> True; _ -> False }) links `shouldBe` True

        it "discovers a structural link between callback and userdata members" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *userdata);"
                , "struct My_Callback { my_cb *cb; void *userdata; };"
                , "void use_cbs(struct My_Callback *handler) {"
                , "    handler->cb(handler->userdata);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)

            let mentionsUserdata = \case
                    InvCallable _ args _ ->
                        any (any (\case { TIdParam _ (Just "userdata") _ -> True; _ -> False }) . Spec.collectTemplates) args
                    _ -> False
            any mentionsUserdata invs `shouldBe` True

        it "discovers links through nested struct access" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct Inner { my_cb *cb; void *u; };"
                , "struct Outer { struct Inner inner; };"
                , "void use(struct Outer *o) {"
                , "    o->inner.cb(o->inner.u);"
                , "}"
                ]
            let res = runAnalysis prog
            let outerInvs = Map.findWithDefault [] "Outer" (irInvariants res)
            let mentionsU = \case
                    InvCallable _ args _ ->
                        any (any (\case { TIdParam _ (Just "u") _ -> True; _ -> False }) . Spec.collectTemplates) args
                    _ -> False
            any mentionsU outerInvs `shouldBe` True

        it "discovers structural links through array indices" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "struct Callbacks { struct My_Callback cbs[10]; };"
                , "void use_cbs(struct Callbacks *cbs, int id) {"
                , "    cbs->cbs[id].cb(cbs->cbs[id].u);"
                , "}"
                ]
            let res = runAnalysis prog

            -- The invariant should be identified for "My_Callback" or "Callbacks"
            -- In this case, "Callbacks" lifts "My_Callback"'s templates.
            let invs = Map.findWithDefault [] "Callbacks" (irInvariants res)
            let isLink = \case { InvCallable {} -> True; InvCoordinatedPair {} -> True; _ -> False }
            any isLink invs `shouldBe` True

        it "discovers equality invariants from assignments" $ do
            prog <- mustParse
                [ "struct Coordinated { void *a; void *b; };"
                , "void sync(struct Coordinated *c) {"
                , "    c->a = c->b;"
                , "}"
                ]
            let res = runAnalysis prog

            let invs = Map.findWithDefault [] "Coordinated" (irInvariants res)
            any (\case { InvEquality {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers links involving address-of operators" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_addr(struct My_Callback *h) {"
                , "    h->cb(&h->u);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers conditional links inside if statements" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_cond(struct My_Callback *h) {"
                , "    if (h->cb) {"
                , "        h->cb(h->u);"
                , "    }"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            let isLink = \case { InvCallable {} -> True; InvCoordinatedPair {} -> True; _ -> False }
            any isLink invs `shouldBe` True

        it "discovers links through variable re-assignments" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_reassign(struct My_Callback *h) {"
                , "    my_cb *c; void *v;"
                , "    c = h->cb;"
                , "    v = h->u;"
                , "    c(v);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "does not promote links between members and unrelated local variables" $ do
            prog <- mustParse
                [ "struct My_Struct { void *u; };"
                , "void leak(struct My_Struct *s, int *p) {"
                , "    s->u = p;"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Struct" (irInvariants res)
            -- This link involves a local variable 'p', so it's not an internal invariant of 'My_Struct'
            invs `shouldBe` []

        it "discovers transitive links through helper function calls" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void helper(my_cb *c, void *v) { c(v); }"
                , "void use_transitive(struct My_Callback *h) {"
                , "    helper(h->cb, h->u);"
                , "}"
                ]
            let res = runAnalysis prog

            -- We expect an invariant for "My_Callback" even though the link is inside 'helper'
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers links between members of different structs (ancestor promotion)" $ do
            prog <- mustParse
                [ "struct Inner { void *ptr; };"
                , "struct Outer { struct Inner *inner; void *data; };"
                , "void f(struct Outer *o) {"
                , "    o->inner->ptr = o->data;"
                , "}"
                ]
            let res = runAnalysis prog

            -- We expect an invariant for "Outer" because it's the common ancestor
            -- and 'ptr' template is lifted to 'Outer'.
            let invs = Map.findWithDefault [] "Outer" (irInvariants res)
            any (\case { InvEquality {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers CoordinatedPair invariants from guarded callback calls" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_coordinated(struct My_Callback *h) {"
                , "    if (h->cb) {"
                , "        h->cb(h->u);"
                , "    }"
                , "}"
                ]
            let res = runAnalysis prog

            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            let isCoordinated :: TS.Invariant 'Global -> Bool
                isCoordinated = \case { InvCoordinatedPair {} -> True; _ -> False }
            any isCoordinated invs `shouldBe` True

        it "discovers transitive links through a deep call chain (reversed order)" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_deep(struct My_Callback *h) {"
                , "    h2(h->cb, h->u);"
                , "}"
                , "void h2(my_cb *c, void *v) { h3(c, v); }"
                , "void h3(my_cb *c, void *v) { c(v); }"
                ]
            let res = runAnalysis prog

            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "does NOT promote links between members of UNRELATED structs" $ do
            prog <- mustParse
                [ "typedef void my_cb_a_cb(void *u);"
                , "struct My_Struct_A { void *u; };"
                , "struct My_Struct_B { my_cb_a_cb *cb; };"
                , "void f(struct My_Struct_A *a, struct My_Struct_B *b) {"
                , "    b->cb(a->u);"
                , "}"
                ]
            let res = runAnalysis prog
            Map.findWithDefault [] "My_Struct_A" (irInvariants res) `shouldBe` []
            Map.findWithDefault [] "My_Struct_B" (irInvariants res) `shouldBe` []

        it "discovers structural links through unions" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "union My_Union { my_cb *cb; void *u; };"
                , "void use_union(union My_Union *u) {"
                , "    u->cb(u->u);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Union" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers CoordinatedPair invariants guarded by loop conditions" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_while(struct My_Callback *h) {"
                , "    while (h->cb) {"
                , "        h->cb(h->u);"
                , "    }"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCoordinatedPair {} -> True; _ -> False }) invs `shouldBe` True

        it "does not grow types infinitely" $ do
            prog <- mustParse
                [ "typedef void some_cb(void *p);"
                , "struct My_Callback { some_cb *cb; void *u; };"
                , "void f(struct My_Callback *h) { h->cb(h->u); g(h); }"
                , "void g(struct My_Callback *h) {"
                , "    struct My_Callback h2;"
                , "    h2.cb = h->cb;"
                , "    h2.u = &h->u;"
                , "    f(&h2);"
                , "}"
                ]
            let res = runAnalysis prog
            irFunctionLinks res `shouldNotBe` Map.empty

        it "discovers structural links through local variable assignment (VarDeclStmt)" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_local(struct My_Callback *h) {"
                , "    struct My_Callback *h2 = h;"
                , "    h2->cb(h2->u);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers links through return values of generic functions" $ do
            prog <- mustParse
                [ "typedef void* get_cb(void *u);"
                , "struct My_Callback { get_cb *cb; void *u; };"
                , "void *use_ret(struct My_Callback *h) {"
                , "    return h->cb(h->u);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            -- We expect the Callable link between cb and u to be discovered even if the result is returned
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers links in nested structs with multiple template owners" $ do
            prog <- mustParse
                [ "struct Nested_Inner { void *ptr; };"
                , "struct Nested_Outer { struct Nested_Inner inner; void *data; };"
                , "void f(struct Nested_Outer *o) {"
                , "    o->inner.ptr = o->data;"
                , "}"
                ]
            let res = runAnalysis prog
            -- Both 'ptr' (owned by Nested_Inner) and 'data' (owned by Nested_Outer) are present.
            -- Nested_Outer lifts 'ptr', so 'ptr' in 'o->inner.ptr' should be owned by Nested_Outer in the context of f.
            let invs = Map.findWithDefault [] "Nested_Outer" (irInvariants res)
            any (\case { InvEquality {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers transitive links through multiple steps of data flow" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_transitive(struct My_Callback *h) {"
                , "    my_cb *c = h->cb;"
                , "    void *v = h->u;"
                , "    void *v2 = v;"
                , "    c(v2);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "converges correctly on cyclic SCCs with stable template IDs" $ do
            -- This test construct should converge in 2 passes if IDs are stable.
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "void h1(my_cb *cb, void *u) { h2(cb, u); }"
                , "void h2(my_cb *cb, void *u) { cb(u); h1(cb, u); }"
                ]
            let res = runAnalysis prog
            let links = Map.findWithDefault [] "h1" (irFunctionLinks res)
            any (\case { InvCallable {} -> True; _ -> False }) links `shouldBe` True

        it "discovers structural links through struct initializers" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_init(my_cb *cb_param, void *u_param) {"
                , "    struct My_Callback h = { cb_param, u_param };"
                , "    h.cb(h.u);"
                , "}"
                ]
            let res = runAnalysis prog
            let links = Map.findWithDefault [] "use_init" (irFunctionLinks res)
            any (\case { InvCallable {} -> True; _ -> False }) links `shouldBe` True

        it "discovers structural links through wrapped return values" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void* get_u(struct My_Callback *h) { return h->u; }"
                , "void use_wrapper(struct My_Callback *h) {"
                , "    h->cb(get_u(h));"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers multiple independent callback/userdata pairs in one struct" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct Multi { my_cb *cb1; void *u1; my_cb *cb2; void *u2; };"
                , "void use_multi(struct Multi *m) {"
                , "    m->cb1(m->u1);"
                , "    m->cb2(m->u2);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "Multi" (irInvariants res)
            -- Should find at least 2 InvCallable invariants (and 2 InvCoordinatedPairs)
            length (filter (\case { InvCallable {} -> True; _ -> False }) invs) `shouldBe` 2
            length (filter (\case { InvCoordinatedPair {} -> True; _ -> False }) invs) `shouldBe` 2

        it "does not incorrectly link unrelated void* fields" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct Unrelated { my_cb *cb; void *u; void *other; };"
                , "void use_unrelated(struct Unrelated *m) {"
                , "    m->cb(m->u);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "Unrelated" (irInvariants res)
            -- Ensure 'other' is not part of any invariant
            let mentionsOther = \case
                    InvCallable _ args _ ->
                        any (any (\case { TIdParam _ (Just "other") _ -> True; _ -> False }) . Spec.collectTemplates) args
                    InvCoordinatedPair _ d1 d2 ->
                        let mentions t = any (\case { TIdParam _ (Just "other") _ -> True; _ -> False }) (Spec.collectTemplates t)
                        in mentions d1 || mentions d2
                    _ -> False
            any mentionsOther invs `shouldBe` False

        it "discovers structural links through multiple return paths (LUB)" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void* get_it(struct My_Callback *h, int choice) {"
                , "    if (choice) return h->cb;"
                , "    return h->u;"
                , "}"
                , "void use_multi_ret(struct My_Callback *h) {"
                , "    my_cb *c = (my_cb *)get_it(h, 1);"
                , "    void *v = get_it(h, 0);"
                , "    c(v);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "correctly distinguishes origins in branched assignments (LUB test)" $ do
            -- In this case, 'v' is only h->u in ONE branch.
            -- If it's overwritten by 'other' in the other branch, and we call cb(v) later,
            -- we might miss the link if we don't merge states correctly.
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; void *other; };"
                , "void use_branch_merge_complex(struct My_Callback *h, int choice) {"
                , "    void *v;"
                , "    if (choice) { v = h->u; } else { v = h->other; }"
                , "    h->cb(v);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            -- If it's path-insensitive and merges correctly, it should find that cb(v)
            -- CAN be cb(h->u), thus promoting the invariant.
            -- Currently, it will only find it if 'v = h->u' was the LAST assignment analyzed.
            let relatesU = \case
                    InvCallable _ args _ ->
                        any (any (\case { TIdParam _ (Just "u") _ -> True; _ -> False }) . Spec.collectTemplates) args
                    _ -> False
            any relatesU invs `shouldBe` True

        it "discovers structural links inside switch statements" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_switch(struct My_Callback *h, int op) {"
                , "    switch (op) {"
                , "        case 1: { h->cb(h->u); break; }"
                , "    }"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers structural links across multiple switch cases" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_switch_multi(struct My_Callback *h, int op) {"
                , "    switch (op) {"
                , "        case 1: { h->cb(h->u); break; }"
                , "        case 2: { h->cb(h->u); break; }"
                , "    }"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers structural links inside do-while statements" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_do(struct My_Callback *h, int choice) {"
                , "    do {"
                , "        h->cb(h->u);"
                , "    } while (choice);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers structural links despite branch-local assignments (state merging)" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_branch_merge(struct My_Callback *h, int choice) {"
                , "    void *v;"
                , "    if (choice) { v = h->u; } else { v = h->u; }"
                , "    h->cb(v);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers path-sensitive CoordinatedPair invariants from Tox_Memory pattern" $ do
            prog <- mustParse
                [ "typedef void tox_memory_dealloc_cb(void *self, void *ptr);"
                , "struct Tox_Memory_Funcs {"
                , "    tox_memory_dealloc_cb *dealloc_callback;"
                , "};"
                , "struct Tox_Memory {"
                , "    struct Tox_Memory_Funcs *funcs;"
                , "    void *user_data;"
                , "};"
                , "void tox_memory_dealloc(struct Tox_Memory *mem, void *ptr)"
                , "{"
                , "    void *user_data = mem->user_data;"
                , "    if (user_data != nullptr) {"
                , "        mem->funcs->dealloc_callback(user_data, ptr);"
                , "    }"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "Tox_Memory" (irInvariants res)
            -- We expect a CoordinatedPair invariant for "Tox_Memory"
            -- triggered by "user_data" (template from mem->user_data)
            let isCoordinatedByUserData = \case
                    InvCoordinatedPair trigger _ _ ->
                        any (\case { TIdParam _ (Just "user_data") _ -> True; _ -> False }) (Spec.collectTemplates trigger)
                    _ -> False
            any isCoordinatedByUserData invs `shouldBe` True

        it "discovers links through deeply nested member access" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct L3 { my_cb *cb; void *u; };"
                , "struct L2 { struct L3 *l3; };"
                , "struct L1 { struct L2 *l2; };"
                , "void use_nested(struct L1 *l1) {"
                , "    l1->l2->l3->cb(l1->l2->l3->u);"
                , "}"
                ]
            let res = runAnalysis prog
            -- The invariant should propagate to L1 because it links members reachable from L1
            let invs = Map.findWithDefault [] "L1" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers structural links from a function returning multiple structs (LUB)" $ do
            prog <- mustParse
                [ "struct My_S { void *u; };"
                , "struct My_S* get_s(struct My_S *s1, struct My_S *s2, int choice) {"
                , "    if (choice) return s1;"
                , "    return s2;"
                , "}"
                , "void use_lub(struct My_S *sa, struct My_S *sb, int choice, void *p) {"
                , "    struct My_S *s = get_s(sa, sb, choice);"
                , "    s->u = p;"
                , "}"
                ]
            let res = runAnalysis prog
            let links = Map.findWithDefault [] "use_lub" (irFunctionLinks res)
            -- 's->u = p' should create a link between p and EITHER sa->u or sb->u.
            -- With Cartesian product handling, both should be found.
            length (filter (\case { InvEquality {} -> True; _ -> False }) links) `shouldSatisfy` (>= 2)

    describe "Advanced Promotion and Guards" $ do
        it "promotes Equality to CoordinatedPair when guarded (path-sensitivity)" $ do
            prog <- mustParse
                [ "struct Guarded { void *trigger; void *a; void *b; };"
                , "void f(struct Guarded *s) {"
                , "    if (s->trigger) {"
                , "        s->a = s->b;"
                , "    }"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "Guarded" (irInvariants res)
            -- Current implementation will only promote it as a simple InvEquality.
            -- It should be an InvCoordinatedPair(trigger, a == b)
            let isCoordinated = \case { InvCoordinatedPair {} -> True; _ -> False }
            any isCoordinated invs `shouldBe` True

        it "discovers links guarded by negated expressions (!ptr)" $ do
            prog <- mustParse
                [ "struct Neg { void *p; void *a; void *b; };"
                , "void f(struct Neg *s) {"
                , "    if (!s->p) return;"
                , "    s->a = s->b;"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "Neg" (irInvariants res)
            -- The relationship a=b is guarded by p being non-null (because it returns if p is null)
            any (\case { InvCoordinatedPair {} -> True; _ -> False }) invs `shouldBe` True

        it "does NOT promote links between different instances of the same struct" $ do
            prog <- mustParse
                [ "struct My_S { void *a; };"
                , "void f(struct My_S *s1, struct My_S *s2) {"
                , "    s1->a = s2->a;"
                , "}"
                ]
            let res = runAnalysis prog
            -- This is a function link, NOT a struct invariant.
            -- Struct invariants must relate templates within ONE instance.
            Map.findWithDefault [] "My_S" (irInvariants res) `shouldBe` []

        it "attributes structural links to the innermost struct (My_Callback)" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *userdata);"
                , "struct My_Callback { my_cb *cb; void *userdata; };"
                , "struct Callbacks { struct My_Callback cbs[10]; };"
                , "void use_cbs(struct Callbacks *cbs, int id) {"
                , "    struct My_Callback *handler = &cbs->cbs[id];"
                , "    handler->cb(handler->userdata);"
                , "}"
                ]
            let res = runAnalysis prog
            -- The invariant relates 'cb' and 'userdata' of 'My_Callback'.
            -- It should be attributed to 'My_Callback' as its primary owner.
            let innerInvs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) innerInvs `shouldBe` True

        it "propagates links through non-generic helper functions" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Struct { my_cb *cb; void *u; };"
                , "void helper(my_cb *c, void *v) { c(v); }"
                , "void use_helper(struct My_Struct *s) {"
                , "    helper(s->cb, s->u);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Struct" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

        it "discovers links through triple indirection (a->b->c->cb)" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct Struct_C { my_cb *cb; void *u; };"
                , "struct Struct_B { struct Struct_C *c; };"
                , "struct Struct_A { struct Struct_B *b; };"
                , "void use_triple(struct Struct_A *a) {"
                , "    a->b->c->cb(a->b->c->u);"
                , "}"
                ]
            let res = runAnalysis prog
            -- Should be attributed to Struct_C (innermost), but also potentially A/B if they lift C.
            let cInvs = Map.findWithDefault [] "Struct_C" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) cInvs `shouldBe` True

        it "discovers structural links despite cast to void* and back" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *u);"
                , "struct My_Callback { my_cb *cb; void *u; };"
                , "void use_cast(struct My_Callback *s) {"
                , "    void *p = s->u;"
                , "    s->cb(p);"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            any (\case { InvCallable {} -> True; _ -> False }) invs `shouldBe` True

    describe "Nested Guards and Tox_Memory" $ do
        it "correctly nests path guards with inherent callback guards" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *self, void *p);"
                , "struct My_Callback { my_cb *_Nonnull cb; void *_Nullable u; };"
                , "void use(struct My_Callback *h, void *p) {"
                , "    if (h->u) {"
                , "        h->cb(h->u, p);"
                , "    }"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Callback" (irInvariants res)
            -- We want to find an InvCoordinatedPair where the trigger is 'u', NOT 'cb'
            let isTriggeredByU = \case
                    InvCoordinatedPair trigger _ _ ->
                        any (\case { TIdParam _ (Just "u") _ -> True; _ -> False }) (Spec.collectTemplates trigger)
                    _ -> False
            any isTriggeredByU invs `shouldBe` True

    describe "Path Sensitivity and Non-Generic Guards" $ do
        it "does NOT promote a link that is guarded by a non-generic variable" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *userdata);"
                , "struct My_Struct { my_cb *cb; void *userdata; int active; };"
                , "void use_s(struct My_Struct *s) {"
                , "    if (s->active) { s->cb(s->userdata); }"
                , "}"
                ]
            let res = runAnalysis prog
            let invs = Map.findWithDefault [] "My_Struct" (irInvariants res)
            -- The link should NOT be promoted because 'active' is not generic,
            -- and the analysis can't represent this guard in the struct's formal parameters.
            invs `shouldBe` []


-- end of file
