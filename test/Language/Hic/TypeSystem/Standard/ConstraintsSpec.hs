{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Standard.ConstraintsSpec (spec) where

import qualified Language.Hic.TypeSystem.Core.Base            as TS

import           Data.Fix                                     (Fix (..))
import           Data.Map.Strict                              (Map)
import qualified Data.Map.Strict                              as Map
import           Data.Text                                    (Text)
import qualified Language.Cimple                              as C
import           Language.Hic.Core.Errors                     (Context (..),
                                                               MismatchReason (..))
import           Language.Hic.TestUtils                       (mustParseNodes)
import           Language.Hic.TypeSystem.Core.Base            (StdType (..),
                                                               TypeInfo,
                                                               TypeRef (..),
                                                               pattern BuiltinType,
                                                               pattern Function,
                                                               pattern Nullable,
                                                               pattern Pointer,
                                                               pattern Singleton,
                                                               pattern Template,
                                                               pattern TypeRef)
import           Language.Hic.TypeSystem.Standard.Constraints
import           Test.Hspec

spec :: Spec
spec = do
    it "extracts constraints from a simple assignment" $ do
        nodes <- mustParseNodes ["void f() { int x; x = 1; }"]
        let (constraints, _, _, _) = extractConstraints Map.empty "test.c" (Fix (C.Group nodes)) 0 0
        let expected = Subtype (Singleton S32Ty 1) (BuiltinType S32Ty) (Just (C.L (C.AlexPn 18 1 19) C.IdVar "x")) [InFunction "f", InFile "test.c"] AssignmentMismatch
        constraints `shouldContain` [expected]

    it "extracts subtyping constraints for pointers" $ do
        nodes <- mustParseNodes ["void f(int *x, int *y) { x = y; }"]
        let (constraints, _, _, _) = extractConstraints Map.empty "test.c" (Fix (C.Group nodes)) 0 0
        let expected = Subtype (Pointer (BuiltinType S32Ty)) (Pointer (BuiltinType S32Ty)) (Just (C.L (C.AlexPn 25 1 26) C.IdVar "x")) [InFunction "f", InFile "test.c"] AssignmentMismatch
        constraints `shouldContain` [expected]

    it "handles member access through constraints" $ do
        nodes <- mustParseNodes ["struct MyStruct { int a; }; void f(struct MyStruct *s) { s->a = 1; }"]
        let (constraints, _, _, _) = extractConstraints Map.empty "test.c" (Fix (C.Group nodes)) 0 0
        -- We expect a HasMember constraint and then a Subtype constraint
        -- The HasMember will relate the struct type to a template variable
        let hasHasMember = any (\case HasMember{} -> True; _ -> False) constraints
        hasHasMember `shouldBe` True

    it "extracts constraints from a statement-like macro" $ do
        nodes <- mustParseNodes
            [ "#define SWAP_INT(x, y) do { int tmp = x; x = y; y = tmp; } while (0)"
            , "void f() { int a = 1; int *b = nullptr; SWAP_INT(a, b); }"
            ]
        let ts = Map.empty
        let (constraints, _, _, _) = extractConstraints ts "test.c" (Fix (C.Group nodes)) 0 0
        -- We expect a Subtype constraint from x = y where x is int and y is int*
        let isMismatchedAssign = \case
                Subtype (Pointer (BuiltinType S32Ty)) (BuiltinType S32Ty) _ _ AssignmentMismatch -> True
                _ -> False
        any isMismatchedAssign constraints `shouldBe` True

    it "extracts constraints for array access with variable index" $ do
        nodes <- mustParseNodes ["void f(void **arr, int i) { void *x = arr[i]; }"]
        let (constraints, _, _, _) = extractConstraints Map.empty "test.c" (Fix (C.Group nodes)) 0 0
        -- We expect x to have a type that is a template indexed by i's type
        let isDependentAssign = \case
                Subtype (Pointer (Template _ (Just (BuiltinType S32Ty)))) _ _ _ InitializerMismatch -> True
                _ -> False
        any isDependentAssign constraints `shouldBe` True

    it "handles polymorphic callbacks with _Nonnull/_Nullable divergence" $ do
        nodes <- mustParseNodes
            [ "typedef struct IP_Port IP_Port;"
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
            , "static int udp_handle_cookie_request(void *_Nonnull object, const IP_Port *_Nonnull source, const uint8_t *_Nonnull packet, uint16_t length, void *_Nullable userdata) {"
            , "    const Net_Crypto *c = (const Net_Crypto *)object;"
            , "    return 0;"
            , "}"
            , "void f(Networking_Core *net, Net_Crypto *temp) {"
            , "    networking_registerhandler(net, 1, &udp_handle_cookie_request, temp);"
            , "}"
            ]
        let (constraints, _, _, _) = extractConstraints Map.empty "test.c" (Fix (C.Group nodes)) 0 0
        -- Verify that we have a Callable constraint relating the callback to the expected type
        let isRegistrationCallable = \case
                Callable (Function _ params) _ _ _ _ _ ->
                    any (\case Nullable (Pointer (TypeRef FuncRef (C.L _ _ tid) _)) -> TS.templateIdToText tid == "packet_handler_cb"; _ -> False) params
                _ -> False
        any isRegistrationCallable constraints `shouldBe` True

