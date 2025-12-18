{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Standard.SolverSpec (spec) where

import           Data.Fix                                     (Fix (..))
import           Data.Map.Strict                              (Map)
import qualified Data.Map.Strict                              as Map
import           Data.Text                                    (Text)
import qualified Data.Text                                    as T
import qualified Language.Cimple                              as C
import           Language.Hic.Core.Errors                     (ErrorInfo (..))
import qualified Language.Hic.Core.Pretty                     as P
import           Language.Hic.TestUtils                       (mustParseNodes)
import qualified Language.Hic.TypeSystem.Core.Base            as TS
import           Language.Hic.TypeSystem.Standard.Constraints (extractConstraints)
import           Language.Hic.TypeSystem.Standard.Solver      (solveConstraints)
import           Test.Hspec
import           Test.QuickCheck                              (within)

spec :: Spec
spec = do
    it "successfully solves Nonnull to Nullable promotion" $ do
        nodes <- mustParseNodes ["void g(int *_Nullable x); void f(int *_Nonnull y) { g(y); }"]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "successfully solves contravariant callback registration (toxcore pattern)" $ within 1000000 $ do
        nodes <- mustParseNodes
            [ "struct IP_Port { int x; };"
            , "typedef struct IP_Port IP_Port;"
            , "struct Networking_Core;"
            , "typedef struct Networking_Core Networking_Core;"
            , "typedef int packet_handler_cb(void *_Nullable object, const IP_Port *_Nonnull source, const uint8_t *_Nonnull packet, uint16_t length, void *_Nullable userdata);"
            , "struct Packet_Handler { packet_handler_cb *function; void *object; };"
            , "typedef struct Packet_Handler Packet_Handler;"
            , "struct Networking_Core { Packet_Handler packethandlers[256]; };"
            , "void networking_registerhandler(Networking_Core *_Nonnull net, uint8_t byte, packet_handler_cb *_Nullable cb, void *_Nullable object) {"
            , "    net->packethandlers[byte].function = cb;"
            , "    net->packethandlers[byte].object = object;"
            , "}"
            , "typedef struct Net_Crypto Net_Crypto;"
            , "struct Net_Crypto { int x; };"
            , "static int udp_handle_cookie_request(void *_Nullable object, const IP_Port *_Nonnull source, const uint8_t *_Nonnull packet, uint16_t length, void *_Nullable userdata) {"
            , "    const Net_Crypto *c = (const Net_Crypto *)object;"
            , "    return 0;"
            , "}"
            , "void f(Networking_Core *_Nonnull net, Net_Crypto *temp) {"
            , "    networking_registerhandler(net, 1, &udp_handle_cookie_request, temp);"
            , "}"
            ]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "successfully solves Nonnull to Nullable covariance" $ do
        nodes <- mustParseNodes ["void g(int *_Nullable x); void f(int *_Nonnull y) { g(y); }"]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "handles unregistration with nullptr" $ do
        nodes <- mustParseNodes
            [ "typedef void my_cb(void *obj);"
            , "struct Reg { my_cb *f; void *o; };"
            , "void set(struct Reg *r, my_cb *f, void *o) { r->f = f; r->o = o; }"
            , "struct My_Data { int x; };"
            , "void handler(void *obj) { struct My_Data *d = (struct My_Data *)obj; }"
            , "void f(struct Reg *r, struct My_Data *d) {"
            , "    set(r, &handler, d);"
            , "    set(r, nullptr, nullptr);"
            , "}"
            ]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "handles heterogeneous registry with indexed templates" $ do
        nodes <- mustParseNodes
            [ "typedef void my_cb(void *obj);"
            , "struct Handler { my_cb *f; void *o; };"
            , "struct Reg { struct Handler h[2]; };"
            , "struct My_A { int a; }; struct My_B { int b; };"
            , "void handlerA(void *obj) { struct My_A *a = (struct My_A *)obj; }"
            , "void handlerB(void *obj) { struct My_B *b = (struct My_B *)obj; }"
            , "void f(struct Reg *r, struct My_A *a, struct My_B *b) {"
            , "    r->h[0].f = &handlerA; r->h[0].o = a;"
            , "    r->h[1].f = &handlerB; r->h[1].o = b;"
            , "}"
            ]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "handles heterogeneous registry with variable index (singleton types)" $ within 1000000 $ do
        nodes <- mustParseNodes
            [ "typedef void my_cb(void *obj);"
            , "struct Handler { my_cb *f; void *o; };"
            , "struct Reg { struct Handler h[256]; };"
            , "void set(struct Reg *r, int i, my_cb *f, void *o) {"
            , "    r->h[i].f = f;"
            , "    r->h[i].o = o;"
            , "}"
            , "struct My_A { int a; }; struct My_B { int b; };"
            , "void handlerA(void *obj) { struct My_A *a = (struct My_A *)obj; }"
            , "void handlerB(void *obj) { struct My_B *b = (struct My_B *)obj; }"
            , "void f(struct Reg *r, struct My_A *a, struct My_B *b) {"
            , "    set(r, 1, &handlerA, a);"
            , "    set(r, 2, &handlerB, b);"
            , "}"
            ]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "reports error for mismatching indices in heterogeneous registry" $ do
        nodes <- mustParseNodes
            [ "struct Reg { void *h[256]; };"
            , "void f(struct Reg *r, int *a, float *b) {"
            , "    r->h[1] = a;"
            , "    r->h[2] = b;"
            , "    r->h[1] = r->h[2];"
            , "}"
            ]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        errors `shouldSatisfy` (not . null)

    it "handles union member access" $ do
        nodes <- mustParseNodes
            [ "union My_Union { int i; float f; };"
            , "void f(union My_Union *u) { u->i = 1; u->f = 1.0; }"
            ]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "reports error for calling a non-function" $ do
        nodes <- mustParseNodes ["void f() { int x = 1; x(); }"]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        errors `shouldSatisfy` (not . null)

    it "handles nested struct initialization with braces" $ do
        nodes <- mustParseNodes
            [ "struct Inner { int x; };"
            , "struct Outer { struct Inner i; };"
            , "void f() { struct Outer o = {{0}}; }"
            ]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "handles ipv6_mreq initialization with deeply nested braces" $ do
        nodes <- mustParseNodes ["void f() { struct ipv6_mreq mreq = {{{{0}}}}; }"]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "prevents infinite recursion via occur-check" $ do
        -- T0 = struct Inner<T0>
        nodes <- mustParseNodes
            [ "struct Inner { void *ptr; };"
            , "void f(struct Inner *i) { i->ptr = i; }"
            ]
        let ts = TS.collect [("test.c", nodes)]
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        let errors = solveConstraints ts constraints
        -- We don't necessarily expect an error here (it's valid C),
        -- but we MUST NOT timeout.
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors

    it "handles ExternalType (e.g. pthread_mutex_t) equality across files" $ do
        let code1 = "int f(pthread_mutex_t *mutex); void g(pthread_mutex_t *m) { f(m); }"
        let code2 = "\n\n\n\n\n\n\n\n\n\nint f(pthread_mutex_t *mutex) { return 0; }"
        nodes1 <- mustParseNodes [code1]
        nodes2 <- mustParseNodes [code2]
        let ts = TS.collect [("f1.c", nodes1), ("f2.c", nodes2)]
        let (c1, _, _, _) = extractConstraints ts "f1.c" (Fix (C.Group nodes1)) 0 0
        let (c2, _, _, _) = extractConstraints ts "f2.c" (Fix (C.Group nodes2)) 0 0
        let errors = solveConstraints ts (c1 ++ c2)
        case errors of
            [] -> return ()
            _  -> expectationFailure $ T.unpack $ T.unlines $ map (P.renderPlain . (\ei -> P.ppErrorInfo "test.c" ei Nothing)) errors
