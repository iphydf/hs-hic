{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Refined.NullabilitySpec (spec) where

import           Data.Text                        (Text)
import qualified Data.Text                        as T
import           GHC.Stack                        (HasCallStack)
import           Language.Hic.Core.Errors         (ErrorInfo (..), NullUse (..),
                                                   TypeError (..))
import           Language.Hic.Refined.BufferSize  (analyseBufferSizes)
import           Language.Hic.Refined.Nullability (checkNullability)
import           Language.Hic.TestUtils           (mustParseNodes)
import           Test.Hspec

-- | The pointers that may be null where they must not be, as "use what",
-- with "null " before those that are null for sure.
nullErrors :: HasCallStack => [Text] -> IO [Text]
nullErrors code = do
    nodes <- mustParseNodes code
    let files = [("test.c", nodes)]
    return [ describe' (errType ei) | ei <- checkNullability (analyseBufferSizes files) files ]

describe' :: TypeError p -> Text
describe' (MayBeNull what use surely) = (if surely then "null " else "") <> useOf use <> " " <> what
  where
    useOf = \case
        Dereferenced   -> "deref"
        Called         -> "call"
        ArgumentOf f i -> f <> "#" <> T.pack (show i)
        StoredIn place -> "store " <> place
        ReturnedFrom f -> "return " <> f
describe' e = T.pack (show e)

shouldReport :: HasCallStack => [Text] -> [Text] -> Expectation
shouldReport code expected = nullErrors code >>= (`shouldMatchList` expected)

spec :: Spec
spec = describe "Nullability" $ do
    describe "what may be null" $ do
        it "reports dereferencing a nullable parameter" $
            [ "int f(const int *_Nullable p) { return *p; }"
            ] `shouldReport` ["deref p"]

        it "accepts dereferencing a nonnull parameter" $
            [ "int f(const int *_Nonnull p) { return *p; }"
            ] `shouldReport` []

        it "takes a pointer declared without either to be nullable" $
            [ "int f(const int *p) { return *p; }"
            ] `shouldReport` ["deref p"]

        it "reports a nullable field, but not a nonnull one" $
            [ "typedef struct Conn { int *_Nullable x; int *_Nonnull y; } Conn;"
            , "int f(const Conn *_Nonnull c) { return *c->y + *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "takes a function declared with a callback type to have that type's parameters" $
            [ "typedef struct Obj { int x; } Obj;"
            , "typedef int obj_cb(Obj *_Nonnull o, const int *_Nullable p);"
            , "static obj_cb handler;"
            , "static int handler(Obj *o, const int *p) { return o->x + *p; }"
            , "void reg(obj_cb *_Nullable *_Nonnull slot) { *slot = handler; }"
            ] `shouldReport` ["deref p"]

        it "takes a typedef said not to be null not to be" $
            [ "typedef uint8_t Key[32];"
            , "void use(const uint8_t key[_Nonnull 32]);"
            , "void f(const Key _Nonnull key) { use(key); }"
            , "void g(const Key _Nullable key) { use(key); }"
            ] `shouldReport` ["use#1 key"]

        it "takes a local array of pointers that can't change, given only addresses, to hold none that are null" $
            [ "typedef struct Pair { int a; int b; } Pair;"
            , "int f(Pair *_Nonnull p, uint32_t j) { int *const fields[] = { &p->a, &p->b }; if (j >= 2) { return 0; } return *fields[j]; }"
            , "int g(int *_Nullable q) { int *const ptrs[] = { q }; return *ptrs[0]; }"
            ] `shouldReport` ["deref ptrs[0]"]

        it "takes what a function returns from its declaration" $
            [ "int *_Nullable get(void);"
            , "int *_Nonnull get_nonnull(void);"
            , "int f(void) { return *get_nonnull() + *get(); }"
            ] `shouldReport` ["deref get()"]

        it "knows addresses, arrays and strings aren't null" $
            [ "void use(const char *_Nonnull p);"
            , "void f(void) { char a[3]; char x; use(a); use(&x); use(\"\"); }"
            ] `shouldReport` []

        it "takes what an array is initialised with as its elements" $
            [ "void f(void) { uint8_t key[32] = {0}; key[0] = 1; }"
            ] `shouldReport` []

        it "knows the names C gives the file and function aren't null" $
            [ "void log_at(const char *_Nonnull file, const char *_Nonnull func);"
            , "void f(void) { log_at(__FILE__, __func__); }"
            ] `shouldReport` []

        it "follows locals from what they're given" $
            [ "int f(int *_Nonnull q, int *_Nullable r) { int *p = q; int *s = r; return *p + *s; }"
            ] `shouldReport` ["deref s"]

        it "reports calling a nullable function pointer" $
            [ "typedef void done_cb(void);"
            , "typedef struct Timer { done_cb *_Nullable done; } Timer;"
            , "void f(const Timer *_Nonnull t) { t->done(); }"
            ] `shouldReport` ["call t->done"]

        it "reports a pointer once, as it isn't null after it's dereferenced" $
            [ "void f(int *_Nullable p) { *p = 1; *p = 2; }"
            ] `shouldReport` ["deref p"]

    describe "where it must not be" $ do
        it "reports a nullable argument to a nonnull parameter" $
            [ "void use(const int *_Nonnull p);"
            , "void f(const int *_Nullable p) { use(p); }"
            ] `shouldReport` ["use#1 p"]

        it "reports nullptr given to a nonnull parameter as null for sure" $
            [ "void use(const int *_Nonnull p);"
            , "void f(void) { use(nullptr); }"
            ] `shouldReport` ["null use#1 nullptr"]

        it "reports a nullable argument to a nonnull array parameter" $
            [ "void use(const uint8_t key[_Nonnull 32]);"
            , "void f(const uint8_t *_Nullable key) { use(key); }"
            ] `shouldReport` ["use#1 key"]

        it "accepts anything for a parameter declared without either" $
            [ "void use(const int *p);"
            , "void f(const int *_Nullable p) { use(p); }"
            ] `shouldReport` []

        it "reports storing nullptr in a nonnull field" $
            [ "typedef struct Conn { int *_Nonnull y; } Conn;"
            , "void f(Conn *_Nonnull c) { c->y = nullptr; }"
            ] `shouldReport` ["null store c->y nullptr"]

        it "reports returning a nullable pointer as nonnull" $
            [ "int *_Nonnull f(int *_Nullable p) { return p; }"
            ] `shouldReport` ["return f p"]

        it "reports a nullable argument for a callback's nonnull parameter" $
            [ "typedef void done_cb(int *_Nonnull p);"
            , "void f(done_cb *_Nonnull done, int *_Nullable p) { done(p); }"
            ] `shouldReport` ["done#1 p"]

    describe "what checks show" $ do
        it "accepts after an early return" $
            [ "int f(const int *_Nullable p) { if (p == nullptr) { return 0; } return *p; }"
            ] `shouldReport` []

        it "accepts inside a check" $
            [ "void use(const int *_Nonnull p);"
            , "void f(const int *_Nullable p) { if (p != nullptr) { use(p); } }"
            ] `shouldReport` []

        it "reports outside a check" $
            [ "void use(const int *_Nonnull p);"
            , "void f(const int *_Nullable p) { if (p != nullptr) { use(p); } use(p); }"
            ] `shouldReport` ["use#1 p"]

        it "reports where a check shows it's null" $
            [ "int f(const int *_Nullable p) { if (p == nullptr) { return *p; } return 0; }"
            ] `shouldReport` ["null deref p"]

        it "follows !, && and ||" $
            [ "int f(const int *_Nullable p, const int *_Nullable q) {"
            , "  if (!p || *p == 0) { return 0; }"
            , "  if (q != nullptr && *q == 0) { return *p; }"
            , "  return *p + *q;"
            , "}"
            ] `shouldReport` ["deref q"]

        it "follows a pointer as a condition" $
            [ "int f(const int *_Nullable p) { if (p) { return *p; } return 0; }"
            ] `shouldReport` []

        it "follows ?:" $
            [ "int f(const int *_Nullable p) { return p != nullptr ? *p : 0; }"
            ] `shouldReport` []

        it "follows an assert" $
            [ "int f(const int *_Nullable p) { assert(p != nullptr); return *p; }"
            ] `shouldReport` []

        it "follows a loop down a list" $
            [ "typedef struct Node { struct Node *_Nullable next; int v; } Node;"
            , "int sum(const Node *_Nullable n) { int s = 0; while (n != nullptr) { s += n->v; n = n->next; } return s; }"
            ] `shouldReport` []

        it "accepts a checked field" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "int f(Conn *_Nonnull c) { if (c->x == nullptr) { return 0; } return *c->x; }"
            ] `shouldReport` []

    describe "what changes" $ do
        it "forgets a checked field after a call, which may change it" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "void touch(Conn *_Nonnull c);"
            , "int f(Conn *_Nonnull c) { if (c->x == nullptr) { return 0; } touch(c); return *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "keeps a checked field across a call that only stores to another" $
            [ "typedef struct Conn { int *_Nullable x; int y; } Conn;"
            , "static void touch_y(Conn *_Nonnull c) { c->y = 1; }"
            , "int f(Conn *_Nonnull c) { if (c->x == nullptr) { return 0; } touch_y(c); return *c->x; }"
            ] `shouldReport` []

        it "forgets a checked field across a call that stores to it, however deep" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "static void clear(Conn *_Nonnull c) { c->x = nullptr; }"
            , "static void outer(Conn *_Nonnull c) { clear(c); }"
            , "int f(Conn *_Nonnull c) { if (c->x == nullptr) { return 0; } outer(c); return *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "keeps a checked callback across unlocking a mutex with the C library" $
            [ "typedef struct Mutex Mutex;"
            , "typedef void done_cb(int n);"
            , "typedef struct Timer { done_cb *_Nullable done; Mutex *_Nonnull mutex; } Timer;"
            , "static void timer_unlock(const Timer *_Nonnull t) { mutex_unlock(t->mutex); }"
            , "void fire(const Timer *_Nonnull t) { if (t->done == nullptr) { return; } timer_unlock(t); t->done(1); }"
            ] `shouldReport` []

        it "takes a store through a parameter to be to what the call gives it" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "static void set_ptr(int *_Nullable *_Nonnull out) { *out = nullptr; }"
            , "int f(Conn *_Nonnull c) { if (c->x == nullptr) { return 0; } int *local = nullptr; set_ptr(&local); return *c->x; }"
            , "int g(Conn *_Nonnull c) { if (c->x == nullptr) { return 0; } set_ptr(&c->x); return *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "forgets an array's element across a call that writes through the array" $
            [ "typedef struct Conn { int *_Nullable ptrs[4]; } Conn;"
            , "static void clear_first(int *_Nullable *_Nonnull p) { *p = nullptr; }"
            , "int f(Conn *_Nonnull c) { if (c->ptrs[0] == nullptr) { return 0; } clear_first(c->ptrs); return *c->ptrs[0]; }"
            ] `shouldReport` ["deref c->ptrs[0]"]

        it "takes a function it can't see the body of to change anything" $
            [ "typedef struct Timer { int *_Nullable p; } Timer;"
            , "void elsewhere(int n);"
            , "int f(const Timer *_Nonnull t) { if (t->p == nullptr) { return 0; } elsewhere(1); return *t->p; }"
            ] `shouldReport` ["deref t->p"]

        it "takes a call through a pointer to be any of the program's functions it can be" $
            [ "typedef struct Conn { int *_Nullable x; int y; } Conn;"
            , "typedef void tick_cb(Conn *_Nonnull c);"
            , "void every(tick_cb *_Nonnull cb);"
            , "static void tick_y(Conn *_Nonnull c) { c->y = 1; }"
            , "static void tick_x(Conn *_Nonnull c) { c->x = nullptr; }"
            , "void start(void) { every(tick_y); every(tick_x); }"
            , "int f(Conn *_Nonnull c, tick_cb *_Nonnull cb) { if (c->x == nullptr) { return 0; } cb(c); return *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "takes allocating through the program's allocator to change nothing" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "typedef void *_Nullable memory_malloc_cb(void *_Nullable self, uint32_t size);"
            , "typedef struct Memory_Funcs { memory_malloc_cb *_Nonnull malloc_callback; } Memory_Funcs;"
            , "typedef struct Memory { const Memory_Funcs *_Nonnull funcs; void *_Nullable user_data; } Memory;"
            , "static void *_Nullable os_malloc(void *_Nonnull self, uint32_t size) { return malloc(size); }"
            , "static const Memory_Funcs os_memory_funcs = { os_malloc };"
            , "typedef void *_Nullable sort_alloc_cb(const void *_Nonnull object, uint32_t count);"
            , "void sort(sort_alloc_cb *_Nonnull alloc);"
            , "static void *_Nullable clearing_alloc(const void *_Nonnull object, uint32_t count) { const Conn *c = (const Conn *)object; ((Conn *)c)->x = nullptr; return nullptr; }"
            , "void g(void) { sort(clearing_alloc); }"
            , "void *_Nullable mem_balloc(const Memory *_Nonnull mem, uint32_t size) { return mem->funcs->malloc_callback(mem->user_data, size); }"
            , "int f(Conn *_Nonnull c, const Memory *_Nonnull mem) { if (c->x == nullptr) { return 0; } mem_balloc(mem, 1); return *c->x; }"
            ] `shouldReport` []

        it "takes a callback the program has none of to be the client's, which may change anything" $
            [ "typedef struct Conn { int *_Nullable x; int y; } Conn;"
            , "typedef void event_cb(int n);"
            , "int f(Conn *_Nonnull c, event_cb *_Nonnull cb) { if (c->x == nullptr) { return 0; } cb(1); return *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "keeps a local across a call that may change anything" $
            [ "typedef void event_cb(int n);"
            , "int f(int *_Nullable p, event_cb *_Nonnull cb) { if (p == nullptr) { return 0; } cb(1); return *p; }"
            ] `shouldReport` []

        it "takes the log callback to change nothing of toxcore's" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "typedef void tox_log_cb(int level, const char *_Nonnull message);"
            , "int f(Conn *_Nonnull c, tox_log_cb *_Nonnull log) { if (c->x == nullptr) { return 0; } log(1, \"hi\"); return *c->x; }"
            ] `shouldReport` []

        it "takes a function's name to be nonnull, also one the program doesn't declare" $
            [ "typedef int cmp_cb(const void *_Nonnull a, const void *_Nonnull b, unsigned long n);"
            , "void use(cmp_cb *_Nonnull cmp);"
            , "void f(void) { use(memcmp); }"
            ] `shouldReport` []

        it "takes a name stored to that the program doesn't declare to be no function" $
            [ "void f(void) { errno = 0; }"
            ] `shouldReport` []

        it "knows an object stored with a callback is there where the callback is" $
            [ "typedef int obj_cb(void *_Nonnull obj, int x);"
            , "typedef struct Conn { obj_cb *_Nullable cb; void *_Nullable cb_object; } Conn;"
            , "void conn_callback(Conn *_Nonnull c, obj_cb *_Nonnull cb, void *_Nonnull object) { c->cb = cb; c->cb_object = object; }"
            , "void conn_clear(Conn *_Nonnull c) { c->cb = nullptr; c->cb_object = nullptr; }"
            , "int f(Conn *_Nonnull c) { if (c->cb != nullptr) { return c->cb(c->cb_object, 1); } return 0; }"
            ] `shouldReport` []

        it "knows that for each struct of its own" $
            [ "typedef int obj_cb(void *_Nonnull obj, int x);"
            , "typedef struct Conn { obj_cb *_Nullable cb; void *_Nullable cb_object; } Conn;"
            , "typedef struct Other { obj_cb *_Nullable cb; } Other;"
            , "void conn_callback(Conn *_Nonnull c, obj_cb *_Nonnull cb, void *_Nonnull object) { c->cb = cb; c->cb_object = object; }"
            , "void other_callback(Other *_Nonnull o, obj_cb *_Nonnull cb) { o->cb = cb; }"
            , "int f(Conn *_Nonnull c) { if (c->cb != nullptr) { return c->cb(c->cb_object, 1); } return 0; }"
            ] `shouldReport` []

        it "doesn't know that where the object is also stored on its own" $
            [ "typedef int obj_cb(void *_Nonnull obj, int x);"
            , "typedef struct Conn { obj_cb *_Nullable cb; void *_Nullable cb_object; } Conn;"
            , "void conn_callback(Conn *_Nonnull c, obj_cb *_Nonnull cb, void *_Nonnull object) { c->cb = cb; c->cb_object = object; }"
            , "void conn_drop(Conn *_Nonnull c) { c->cb_object = nullptr; }"
            , "int f(Conn *_Nonnull c) { if (c->cb != nullptr) { return c->cb(c->cb_object, 1); } return 0; }"
            ] `shouldReport` ["c->cb#1 c->cb_object"]

        it "knows what a call stores through an out-parameter where it returns what it returns then" $
            [ "typedef struct Pkt { int x; } Pkt;"
            , "static int get(Pkt *_Nullable *_Nonnull out, Pkt *_Nullable p) { if (p == nullptr) { return 0; } *out = p; return 1; }"
            , "int f(Pkt *_Nullable p) { Pkt *q = nullptr; const int ret = get(&q, p); if (ret == 1) { return q->x; } return 0; }"
            , "int g(Pkt *_Nullable p) { Pkt *q; if (get(&q, p) == 1) { return q->x; } return 0; }"
            , "int h(Pkt *_Nullable p) { Pkt *q; if (get(&q, p) != 0 && q->x == 1) { return 1; } return 0; }"
            , "int k(Pkt *_Nullable p) { Pkt *q = nullptr; const int ret = get(&q, p); if (ret == 0) { return q->x; } return 0; }"
            , "static int put(Pkt *_Nonnull *_Nonnull out, Pkt *_Nullable p) { if (p == nullptr) { return 0; } *out = p; return 1; }"
            , "int m(Pkt *_Nullable p) { Pkt *q = nullptr; if (put(&q, p) == 1 && q->x == 1) { return 1; } return 0; }"
            , "static int find(Pkt *_Nonnull *_Nonnull out, Pkt *_Nullable p, int n) { if (n < 0) { return -1; } if (p == nullptr) { return 0; } *out = p; return 1; }"
            , "int s(Pkt *_Nullable p, int n);"
            , "int s(Pkt *_Nullable p, int n) { Pkt *q; const int ret = find(&q, p, n); if (ret == -1) { return -1; } if (ret == 0) { return 0; } return q->x; }"
            , "static uint16_t take(Pkt *_Nullable *_Nonnull out, Pkt *_Nullable p, uint16_t n) { if (p == nullptr || n == 0) { return 0; } *out = p; return n; }"
            , "int t(Pkt *_Nullable p, uint16_t n);"
            , "int t(Pkt *_Nullable p, uint16_t n) { Pkt *q = nullptr; const uint16_t len = take(&q, p, n); if (len == 0) { return 0; } return q->x; }"
            ] `shouldReport` ["deref q"]

        it "expands a macro to see what it calls" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "static void clear(Conn *_Nonnull c) { c->x = nullptr; }"
            , "#define CLEAR(c) clear(c)"
            , "int f(Conn *_Nonnull c) { if (c->x == nullptr) { return 0; } CLEAR(c); return *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "expands a macro as it's defined where it's used" $
            [ "typedef struct Saved { int a; } Saved;"
            , "static int size(void) {"
            , "    int n = 0;"
            , "    const Saved *const s = nullptr;"
            , "#define MEMBER(n, x) do { n += sizeof(x); } while (0)"
            , "    MEMBER(n, s->a);"
            , "#undef MEMBER"
            , "    return n;"
            , "}"
            , "static int sum(const Saved *_Nonnull s) {"
            , "    int n = 0;"
            , "#define MEMBER(n, x) do { n += x; } while (0)"
            , "    MEMBER(n, s->a);"
            , "#undef MEMBER"
            , "    return n;"
            , "}"
            ] `shouldReport` []

        it "follows a check inside a macro" $
            [ "#define SET_ERROR(param, x) do { if (param != nullptr) { *param = x; } } while (0)"
            , "void f(int *_Nullable error) { SET_ERROR(error, 1); }"
            ] `shouldReport` []

        it "forgets a checked field after its object changes" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "int f(Conn *_Nonnull c, Conn *_Nonnull d) { if (c->x == nullptr) { return 0; } c = d; return *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "forgets a checked field after a store to the same field elsewhere" $
            [ "typedef struct Conn { int *_Nullable x; } Conn;"
            , "int f(Conn *_Nonnull c, Conn *_Nonnull d) { if (c->x == nullptr) { return 0; } d->x = nullptr; return *c->x; }"
            ] `shouldReport` ["deref c->x"]

        it "keeps a checked field after a store to another" $
            [ "typedef struct Conn { int *_Nullable x; int *_Nullable y; } Conn;"
            , "int f(Conn *_Nonnull c, Conn *_Nonnull d) { if (c->x == nullptr) { return 0; } d->y = nullptr; return *c->x; }"
            ] `shouldReport` []

    describe "buffers with lengths" $ do
        it "accepts a nullable buffer whose length is known to be at least 1" $
            [ "int f(const uint8_t *_Nullable data, uint16_t length) { if (length < 2) { return -1; } return data[1]; }"
            ] `shouldReport` []

        it "reports one whose length isn't" $
            [ "int f(const uint8_t *_Nullable data, uint16_t length) { return data[0]; }"
            ] `shouldReport` ["deref data"]

        it "reports one the function changes" $
            [ "int f(const uint8_t *_Nullable data, uint16_t length, const uint8_t *_Nullable other) {"
            , "  if (length < 2) { return -1; }"
            , "  data = other;"
            , "  return data[0];"
            , "}"
            ] `shouldReport` ["deref data"]

        it "accepts a field whose length field is checked" $
            [ "typedef struct Buf { uint8_t *_Nullable data; uint32_t data_length; } Buf;"
            , "int f(const Buf *_Nonnull b) { if (b->data_length == 0) { return 0; } return b->data[0]; }"
            ] `shouldReport` []

        it "accepts an array indexed below its count" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *_Nullable peers; uint32_t num_peers; } Group;"
            , "int f(const Group *_Nonnull g, uint32_t i) { if (i >= g->num_peers) { return -1; } return g->peers[i].x; }"
            ] `shouldReport` []

        it "knows a count checked earlier in the same expression" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *_Nullable peers; uint32_t num_peers; } Group;"
            , "bool f(const Group *_Nonnull g, uint32_t i) { return i < g->num_peers && g->peers[i].x == 0; }"
            , "int h(const Group *_Nonnull g, uint32_t i) { return i < g->num_peers ? g->peers[i].x : 0; }"
            , "bool k(const Group *_Nonnull g, uint32_t i) { return i < g->num_peers || g->peers[i].x == 0; }"
            ] `shouldReport` ["deref g->peers"]

        it "trusts a field until the function stores to it" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *_Nullable peers; uint32_t num_peers; } Group;"
            , "int f(Group *_Nonnull g, uint32_t n) {"
            , "  for (uint32_t i = 0; i < g->num_peers; ++i) { if (g->peers[i].x == 0) { return 1; } }"
            , "  g->num_peers = n;"
            , "  return -1;"
            , "}"
            ] `shouldReport` []

        it "knows a counted array has what its count said where the function started" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *_Nullable peers; uint32_t num_peers; } Group;"
            , "void set(Group *_Nonnull g, Peer *_Nonnull peers, uint32_t num_peers);"
            , "void set(Group *_Nonnull g, Peer *_Nonnull peers, uint32_t num_peers) { g->peers = peers; g->num_peers = num_peers; }"
            , "void f(Group *_Nonnull g, uint32_t i);"
            , "void f(Group *_Nonnull g, uint32_t i) {"
            , "  if (i >= g->num_peers) { return; }"
            , "  --g->num_peers;"
            , "  if (g->num_peers != i) { g->peers[i] = g->peers[g->num_peers]; }"
            , "}"
            ] `shouldReport` []

        it "reports what may be null stored to a counted array, but not nullptr" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *_Nullable peers; uint32_t num_peers; } Group;"
            , "void f(Group *_Nonnull g, Peer *_Nullable p) { g->peers = p; }"
            , "void h(Group *_Nonnull g) { g->peers = nullptr; g->num_peers = 0; }"
            , "void k(Group *_Nonnull g, Peer *_Nullable peers, uint32_t num_peers) { g->peers = peers; g->num_peers = num_peers; }"
            ] `shouldReport` ["store g->peers p"]

        it "doesn't trust a field the function stores to in an earlier turn of a loop" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *_Nullable peers; uint32_t num_peers; } Group;"
            , "void f(Group *_Nonnull g, uint32_t n) {"
            , "  for (uint32_t i = 0; i < n; ++i) { if (g->num_peers > 0) { g->peers[0].x = 1; } g->num_peers = i; }"
            , "}"
            ] `shouldReport` ["deref g->peers"]

        it "doesn't trust a field the function stores to" $
            [ "typedef struct Buf { uint8_t *_Nullable data; uint32_t data_length; } Buf;"
            , "int f(Buf *_Nonnull b, uint8_t *_Nullable other) { if (b->data_length == 0) { return 0; } b->data = other; return b->data[0]; }"
            ] `shouldReport` ["store b->data other"]

        it "knows a VLA isn't null" $
            [ "void use(const uint8_t *_Nonnull p);"
            , "void f(uint16_t n) { VLA(uint8_t, buf, n); use(buf); }"
            ] `shouldReport` []
