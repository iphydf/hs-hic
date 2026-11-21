{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Refined.BufferSizeSpec (spec) where

import qualified Data.Map.Strict                          as Map
import           Data.Text                                (Text)
import qualified Data.Text                                as T
import           GHC.Stack                                (HasCallStack)
import qualified Language.Cimple                          as C
import           Language.Hic.Core.Errors                 (ErrorInfo (..),
                                                           TypeError (..))
import           Language.Hic.Inference                   (lower)
import           Language.Hic.Inference.Engine            (inferProgram)
import           Language.Hic.Refined.BufferSize          (checkBufferSizes)
import           Language.Hic.Refined.BufferSize.Integers (Range (..),
                                                           rangeArith,
                                                           unknownRange)
import           Language.Hic.TestUtils                   (mustParse,
                                                           mustParseNodes)
import           Test.Hspec

-- | The calls whose arguments can't be shown to be big enough, as
-- "function#argument needs/known".
sizeErrors :: HasCallStack => [Text] -> IO [Text]
sizeErrors code = do
    nodes <- mustParseNodes code
    return [ describe' (errType ei) | ei <- checkBufferSizes [("test.c", nodes)] ]

-- | The same of what inference makes of the code, lowered back to C as the
-- checker is given it.
loweredSizeErrors :: HasCallStack => [Text] -> IO [Text]
loweredSizeErrors code = do
    prog <- mustParse code
    return [ describe' (errType ei) | ei <- checkBufferSizes [ (f, map lower ns) | (f, ns) <- Map.toList (fst (inferProgram prog)) ] ]

-- | The lines reports are on, directly and of what inference makes of the
-- code.
errorLines :: HasCallStack => [Text] -> IO ([Int], [Int])
errorLines code = do
    nodes <- mustParseNodes code
    prog <- mustParse code
    let lowered = [ (f, map lower ns) | (f, ns) <- Map.toList (fst (inferProgram prog)) ]
        lineOf ei = maybe 0 (\(C.L (C.AlexPn _ l _) _ _) -> l) (errLoc ei)
    return (map lineOf (checkBufferSizes [("test.c", nodes)]), map lineOf (checkBufferSizes lowered))

describe' :: TypeError p -> Text
describe' (ArgumentTooShort f i needed known) =
    f <> "#" <> T.pack (show i) <> " needs " <> T.pack (show needed) <> ", " <> maybe "unknown" (("has " <>) . T.pack . show) known
describe' (ArgumentTooSmall f i needed known) =
    f <> "#" <> T.pack (show i) <> " at least " <> T.pack (show needed) <> ", " <> maybe "unknown" (("is " <>) . T.pack . show) known
describe' (ArgumentTooBig f i needed known) =
    f <> "#" <> T.pack (show i) <> " at most " <> T.pack (show needed) <> ", " <> maybe "unknown" (("is " <>) . T.pack . show) known
describe' (PointeeTooBig f i needed known) =
    f <> "#" <> T.pack (show i) <> " points to at most " <> T.pack (show needed) <> ", " <> maybe "unknown" (("is " <>) . T.pack . show) known
describe' (SignedOverflow lo hi _ _) =
    "overflow " <> maybe "any" (T.pack . show) lo <> ".." <> maybe "any" (T.pack . show) hi
describe' (AssertMayFail cond) = "assert " <> cond
describe' (ArgumentsUnbalanced f terms c known) =
    f <> " " <> T.unwords [ T.pack (show n) <> "*#" <> T.pack (show i) | (n, i) <- terms ] <> " " <> T.pack (show c)
        <> ", " <> maybe "unknown" (("least " <>) . T.pack . show) known
describe' (ArgumentShorterThanLength f i j known most) =
    f <> "#" <> T.pack (show i) <> " vs #" <> T.pack (show j) <> ": " <> maybe "unknown" (("has " <>) . T.pack . show) known
        <> ", " <> maybe "any length" (("up to " <>) . T.pack . show) most
describe' (ArgumentShorterThanNeeded f i known most) =
    f <> "#" <> T.pack (show i) <> " needs: " <> maybe "unknown" (("has " <>) . T.pack . show) known
        <> ", " <> maybe "any length" (("up to " <>) . T.pack . show) most
describe' (BufferShorterThanLength buf len known most) =
    buf <> " vs " <> len <> ": " <> maybe "unknown" (("has " <>) . T.pack . show) known
        <> ", " <> maybe "any length" (("up to " <>) . T.pack . show) most
describe' (CountAboveCapacity count capacity) = count <> " over " <> capacity
describe' (IndexOutOfBounds arr ix known least most) =
    "index " <> arr <> "[" <> ix <> "]: " <> maybe "unknown" (("has " <>) . T.pack . show) known
        <> ", " <> maybe "any" (T.pack . show) least <> ".." <> maybe "any" (T.pack . show) most
describe' (PointerPastEnd ptr by known least most) =
    "past " <> ptr <> " + " <> by <> ": " <> maybe "unknown" (("has " <>) . T.pack . show) known
        <> ", " <> maybe "any" (T.pack . show) least <> ".." <> maybe "any" (T.pack . show) most
describe' (NegativeToUnsigned what ty least) =
    "unsigned " <> what <> " to " <> ty <> ", least " <> maybe "any" (T.pack . show) least
describe' (TooBigForSigned what ty most) =
    "signed " <> what <> " to " <> ty <> ", most " <> maybe "any" (T.pack . show) most
describe' e = T.pack (show e)

shouldBeShort :: HasCallStack => [Text] -> [Text] -> Expectation
shouldBeShort code expected = sizeErrors code >>= (`shouldMatchList` expected)

spec :: Spec
spec = describe "Buffer sizes" $ do
    describe "where sizes come from" $ do
        it "accepts a local array of the right size" $
            [ "void use(const uint8_t key[32]);"
            , "void f(void) { uint8_t key[32]; use(key); }"
            ] `shouldBeShort` []

        it "reports a local array that is too small" $
            [ "void use(const uint8_t key[32]);"
            , "void f(void) { uint8_t key[16]; use(key); }"
            ] `shouldBeShort` ["use#1 needs 32, has 16"]

        it "reports a pointer parameter, whose size isn't known" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t *key) { use(key); }"
            ] `shouldBeShort` ["use#1 needs 32, has 1"]

        it "accepts an array parameter with a size passed on" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t key[32]) { use(key); }"
            ] `shouldBeShort` []

        it "evaluates sizes given by constants" $
            [ "#define KEY_SIZE 32"
            , "#define NONCE_SIZE (KEY_SIZE - 8)"
            , "void use(const uint8_t nonce[NONCE_SIZE]);"
            , "void f(void) { uint8_t key[KEY_SIZE]; use(key); }"
            ] `shouldBeShort` []

        it "evaluates sizes given by enumerators" $
            [ "typedef enum Sizes { SIZE_SMALL = 4, SIZE_BIG } Sizes;"
            , "void use(const uint8_t b[SIZE_BIG]);"
            , "void f(void) { uint8_t s[SIZE_SMALL]; use(s); }"
            ] `shouldBeShort` ["use#1 needs 5, has 4"]

        it "counts at least the fields of a struct in its size" $
            [ "typedef struct Inner { uint32_t a; uint8_t b[4]; } Inner;"
            , "typedef struct Outer { uint8_t key[32]; Inner inner; } Outer;"
            , "#define MAX_LENGTH (1 + sizeof(Outer) * 2)"
            , "void use(const uint8_t key[32]);"
            , "void f(void) { uint8_t plain[MAX_LENGTH]; use(plain + 1 + 40 + 40 - 32); }"
            ] `shouldBeShort` []

        it "doesn't take a struct's size as what a parameter needs" $
            [ "typedef struct Pair { uint32_t a; uint32_t b; } Pair;"
            , "void use(const uint8_t p[sizeof(Pair)]);"
            , "void f(void) { uint8_t buf[8]; use(buf); }"
            ] `shouldBeShort` []

        it "doesn't take the smallest size of size_t as what a parameter needs" $
            [ "void use(const uint8_t p[sizeof(size_t)]);"
            , "void f(void) { uint8_t buf[4]; use(buf); }"
            ] `shouldBeShort` ["use#1 needs 8, has 4"]

        it "keeps the size of a type in the size of a local array" $
            [ "typedef struct Thing { void *p; uint32_t n; } Thing;"
            , "void use(const uint8_t *data, uint16_t length);"
            , "void f(void) { uint8_t buf[sizeof(Thing) * 2]; use(buf, sizeof(Thing) * 2); use(buf + sizeof(Thing), sizeof(Thing)); use(buf, sizeof(buf)); }"
            , "void g(void) { uint16_t nums[sizeof(Thing)]; use((uint8_t *)nums, sizeof(nums)); }"
            ] `shouldBeShort` []

        it "takes the size of a field that is an array" $
            [ "typedef struct Peer { uint8_t pk[32]; } Peer;"
            , "void use(const uint8_t key[32]);"
            , "void f(const Peer *p) { use(p->pk); }"
            ] `shouldBeShort` []

        it "takes the size of what a function returns" $
            [ "typedef struct Peer { uint8_t pk[32]; } Peer;"
            , "void use(const uint8_t key[32]);"
            , "static const uint8_t *peer_key(const Peer *p) { return p->pk; }"
            , "void f(const Peer *p) { use(peer_key(p)); }"
            ] `shouldBeShort` []

        it "takes the size of what a pointer set in a loop points to" $
            [ "typedef struct Entry { uint8_t key[32]; } Entry;"
            , "void use(const uint8_t key[32]);"
            , "static const uint8_t *find(const Entry *entries, int entries_count) {"
            , "    const uint8_t *found = nullptr;"
            , "    for (int i = 0; i < entries_count; ++i) {"
            , "        if (entries[i].key[0] == 1) { found = entries[i].key; break; }"
            , "    }"
            , "    return found;"
            , "}"
            , "void f(const Entry e[3]) { const uint8_t *k = find(e, 3); use(k); }"
            ] `shouldBeShort` []

        it "takes the size of a pointer field from what is put in it" $
            [ "typedef struct Dht { uint8_t pk[32]; } Dht;"
            , "typedef struct Announce { const uint8_t *public_key; } Announce;"
            , "void use(const uint8_t key[32]);"
            , "void init(Announce *a, const Dht *d) { a->public_key = d->pk; }"
            , "void f(const Announce *a) { use(a->public_key); }"
            ] `shouldBeShort` []

        it "doesn't know a pointer field's size when something unknown is put in it" $
            [ "typedef struct Announce { const uint8_t *public_key; } Announce;"
            , "void use(const uint8_t key[32]);"
            , "void init(Announce *a, const uint8_t *pk) { a->public_key = pk; }"
            , "void f(const Announce *a) { use(a->public_key); }"
            ] `shouldBeShort` ["use#1 needs 32, has 1"]

        it "checks calls through a function pointer" $
            [ "typedef void key_cb(const uint8_t key[32]);"
            , "void f(key_cb *cb, const uint8_t *p) { cb(p); }"
            ] `shouldBeShort` ["key_cb#1 needs 32, has 1"]

    describe "pointers into a buffer" $ do
        it "takes an offset off the size" $
            [ "void use(const uint8_t key[32]);"
            , "void f(void) { uint8_t packet[33]; use(packet + 1); use(&packet[2]); }"
            ] `shouldBeShort` ["use#1 needs 32, has 31"]

        it "follows a local pointer into a buffer" $
            [ "void use(const uint8_t key[32]);"
            , "void f(void) { uint8_t packet[40]; const uint8_t *pk = packet + 8; use(pk); }"
            ] `shouldBeShort` []

        it "measures a buffer by the length after it" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t *data, uint16_t length) { use(data + 1); }"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past data + 1: has 0, 1..1"]

        it "knows the length after a guard" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    if (length < 33) { return -1; }"
            , "    use(data + 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows the length after an exact guard with a sum" $
            [ "#define KEY_SIZE 32"
            , "void use(const uint8_t key[KEY_SIZE]);"
            , "int f(const uint8_t data[], uint16_t length) {"
            , "    if (data == nullptr || length != 1 + KEY_SIZE) { return -1; }"
            , "    use(data + 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows the length after a guard on a length made from it" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    const int32_t rest = (int32_t)length - 1;"
            , "    if (rest < 32) { return -1; }"
            , "    use(data + 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows the length after a guard on a length made from one made from it" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    const int32_t rest = (int32_t)length - 1;"
            , "    const int32_t last = rest - 31;"
            , "    if (last < 1) { return -1; }"
            , "    use(data + 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "keeps what a branch knew about a pointer that is null on the other" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    const uint8_t *hash = nullptr;"
            , "    if (length == 64) { hash = data + 32; }"
            , "    if (hash != nullptr) { use(hash); }"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows the size of a VLA from a guard on a length made from the same one" $
            [ "void use(const uint8_t key[32]);"
            , "int f(uint16_t length) {"
            , "    const int32_t plain_len = (int32_t)length - 1;"
            , "    const int32_t rest = plain_len - 32;"
            , "    if (rest < 0) { return -1; }"
            , "    VLA(uint8_t, plain, plain_len);"
            , "    use(plain);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows the smallest length when a guard allows several" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    if (length != 32 && length != 64) { return -1; }"
            , "    use(data);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows the length after a guard on what a function returns" $
            [ "void use(const uint8_t key[32]);"
            , "static uint32_t key_data_size(void) { return sizeof(uint32_t) + 32; }"
            , "int f(const uint8_t *data, uint32_t length) {"
            , "    if (length != key_data_size()) { return -1; }"
            , "    use(data + sizeof(uint32_t));"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "doesn't trust a guard through a cast that can wrap" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    if ((uint32_t)(length - 1) < 32) { return -1; }"
            , "    use(data + 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["unsigned (length - 1) to uint32_t, least -1", "use#1 needs 32, has 0", "past data + 1: has 0, 1..1"]

        it "trusts a guard through a cast that can't wrap" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    if ((int32_t)length - 1 < 32) { return -1; }"
            , "    use(data + 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "doesn't know the length in the branch the guard leaves" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t *data, uint16_t length) {"
            , "    if (length < 33) { use(data + 1); }"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past data + 1: has 0, 1..1"]

        it "follows a cursor and its length through a loop" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t *data, uint16_t length) {"
            , "    while (length >= 32) {"
            , "        use(data);"
            , "        data += 32;"
            , "        length -= 32;"
            , "    }"
            , "}"
            ] `shouldBeShort` []

        it "follows a cursor and its length moved by an amount read into an out-parameter" $
            [ "void use(const uint8_t key[4]);"
            , "void sub(const uint8_t *data, uint32_t length);"
            , "void read(uint32_t *dest, const uint8_t key[4]) { memcpy(dest, key, 4); }"
            , "int f(const uint8_t *data, uint32_t length) {"
            , "    while (length >= 8) {"
            , "        uint32_t length_sub;"
            , "        read(&length_sub, data);"
            , "        use(data + 4);"
            , "        data += 8;"
            , "        length -= 8;"
            , "        if (length < length_sub) { return -1; }"
            , "        sub(data, length_sub);"
            , "        data += length_sub;"
            , "        length -= length_sub;"
            , "    }"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "follows a cursor moved a step each time round a loop" $
            [ "void use(const uint8_t key[32]);"
            , "void f(void) {"
            , "    uint8_t buf[64];"
            , "    const uint8_t *p = buf;"
            , "    for (int i = 0; i < 4; ++i) {"
            , "        use(p);"
            , "        p += 16;"
            , "    }"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 16"]

    describe "allocated buffers" $ do
        let allocators =
                [ "GNU_ALLOC_SIZE(2) void *mem_balloc(const Memory *mem, uint32_t size);"
                , "GNU_ALLOC_SIZE(2, 3) void *mem_valloc(const Memory *mem, uint32_t nmemb, uint32_t size);"
                , "void use(const uint8_t key[32]);"
                ]
        it "takes the size of an allocation from its size argument" $
            (allocators ++
            [ "void f(const Memory *mem) {"
            , "    uint8_t *p = (uint8_t *)mem_balloc(mem, 40);"
            , "    use(p + 8);"
            , "}"
            ]) `shouldBeShort` []

        it "reports an allocation that is too small" $
            (allocators ++
            [ "void f(const Memory *mem) {"
            , "    uint8_t *p = (uint8_t *)mem_balloc(mem, 16);"
            , "    use(p);"
            , "}"
            ]) `shouldBeShort` ["use#1 needs 32, has 16"]

        it "takes the size of an allocation from a checked length" $
            (allocators ++
            [ "void f(const Memory *mem, uint32_t length) {"
            , "    if (length < 32) { return; }"
            , "    uint8_t *p = (uint8_t *)mem_balloc(mem, length);"
            , "    use(p);"
            , "}"
            ]) `shouldBeShort` []

        it "counts the elements of an allocation of an array" $
            (allocators ++
            [ "typedef struct Pair { uint8_t a[32]; uint8_t b[32]; } Pair;"
            , "void use_pairs(const Pair pairs[2]);"
            , "void f(const Memory *mem) {"
            , "    Pair *pairs = (Pair *)mem_valloc(mem, 2, sizeof(Pair));"
            , "    use_pairs(pairs);"
            , "}"
            ]) `shouldBeShort` []

        it "takes the size of an allocation of the type it returns" $
            [ "GNU_ALLOC_SIZE(3) uint8_t *memdup(const Memory *mem, const uint8_t *data, size_t data_size);"
            , "void use(const uint8_t *data, uint16_t length);"
            , "void f(const Memory *mem, const uint8_t *data, uint16_t length) {"
            , "    uint8_t *copy = memdup(mem, data, length);"
            , "    if (copy == nullptr) { return; }"
            , "    use(copy, length);"
            , "}"
            ] `shouldBeShort` []

        it "doesn't take the memory given to a reallocation to have its new size" $
            [ "GNU_ALLOC_SIZE(3) void *mem_brealloc(const Memory *mem, void *ptr, uint32_t size);"
            , "void *f(const Memory *mem, void *ptr, uint32_t size) { return mem_brealloc(mem, ptr, size + 1); }"
            ] `shouldBeShort` []

        it "takes the size of an allocation from a callback of an allocator type" $
            [ "GNU_ALLOC_SIZE(2) typedef void *alloc_cb(void *self, uint32_t size);"
            , "GNU_ALLOC_SIZE(3) typedef void *realloc_cb(void *self, void *ptr, uint32_t size);"
            , "typedef struct Funcs { alloc_cb *alloc; realloc_cb *resize; } Funcs;"
            , "void use(const uint8_t key[32]);"
            , "void f(const Funcs *funcs, void *self, void *old) {"
            , "    uint8_t *p = (uint8_t *)funcs->alloc(self, 40);"
            , "    uint8_t *q = (uint8_t *)funcs->resize(self, old, 16);"
            , "    if (p == nullptr || q == nullptr) { return; }"
            , "    use(p);"
            , "    use(q);"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 16"]

        it "knows the C library's allocators" $
            [ "void use(const uint8_t key[32]);"
            , "void f(void) {"
            , "    uint8_t *p = (uint8_t *)malloc(40);"
            , "    uint8_t *q = (uint8_t *)calloc(2, 16);"
            , "    if (p == nullptr || q == nullptr) { return; }"
            , "    use(p);"
            , "    use(q);"
            , "    uint8_t *r = (uint8_t *)realloc(q, 16);"
            , "    if (r == nullptr) { return; }"
            , "    use(r);"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 16"]

    describe "cursors" $ do
        it "follows a cursor checked against what's left of its buffer" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    const uint8_t *d = data;"
            , "    while ((unsigned int)(length - (d - data)) >= 2 + 32 * 2 + 1) {"
            , "        d += 2;"
            , "        use(d);"
            , "        use(d + 32);"
            , "        d += 32 * 2;"
            , "        const uint8_t name_length = *d;"
            , "        d += 1;"
            , "        if (name_length > (length - (d - data))) { return -1; }"
            , "        d += name_length;"
            , "    }"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "doesn't trust a wrapping check when the cursor can pass the end" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    const uint8_t *d = data;"
            , "    while ((unsigned int)(length - (d - data)) >= 2 + 32 * 2 + 1) {"
            , "        d += 2;"
            , "        use(d);"
            , "        d += 32 * 2;"
            , "        const uint8_t name_length = *d;"
            , "        d += 1;"
            , "        d += name_length;"
            , "    }"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["unsigned (length - (d - data)) to unsigned int, least -2147483648", "use#1 needs 32, unknown", "overflow -9223372036854775807..65535"]

        it "follows a cursor measured from where it started" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint32_t length, uint32_t count) {"
            , "    const uint8_t *init_data = data;"
            , "    if (length < 2) { return 0; }"
            , "    ++data;"
            , "    const uint8_t title_len = *data;"
            , "    ++data;"
            , "    if (length - (uint32_t)(data - init_data) < title_len) { return 0; }"
            , "    data += title_len;"
            , "    for (uint32_t j = 0; j < count; ++j) {"
            , "        if (length - (uint32_t)(data - init_data) < 64) { return 0; }"
            , "        use(data);"
            , "        data += 32;"
            , "        use(data);"
            , "        data += 32;"
            , "    }"
            , "    return 1;"
            , "}"
            ] `shouldBeShort` []

        it "doesn't trust a guard on where a cursor would be that can wrap" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint32_t length, uint32_t skip) {"
            , "    const uint8_t *init_data = data;"
            , "    if (length < skip) { return 0; }"
            , "    data += skip;"
            , "    if (length < (uint32_t)(data - init_data) + 32) { return 0; }"
            , "    use(data);"
            , "    return 1;"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0"]

    describe "what static functions need from their callers" $ do
        it "lets a static function rely on its callers' length checks" $
            [ "void use(const uint8_t key[32]);"
            , "static int helper(const uint8_t *data, uint16_t length) { use(data + 1); return 0; }"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    if (length != 40) { return -1; }"
            , "    return helper(data, length);"
            , "}"
            ] `shouldBeShort` []

        it "reports a caller that doesn't check" $
            [ "void use(const uint8_t key[32]);"
            , "static int helper(const uint8_t *data, uint16_t length) { use(data + 1); return 0; }"
            , "int f(const uint8_t *data, uint16_t length) { return helper(data, length); }"
            ] `shouldBeShort` ["helper#2 at least 33, is 0"]

        it "passes what a static function needs up to its static callers" $
            [ "void use(const uint8_t key[32]);"
            , "static int helper(const uint8_t *data, uint16_t length) { use(data + 1); return 0; }"
            , "static int middle(const uint8_t *data, uint16_t length) { return helper(data, length); }"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    if (length < 33) { return -1; }"
            , "    return middle(data, length);"
            , "}"
            ] `shouldBeShort` []

        it "doesn't let a function rely on callers it can't see" $
            [ "void use(const uint8_t key[32]);"
            , "int helper(const uint8_t *data, uint16_t length) { use(data + 1); return 0; }"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past data + 1: has 0, 1..1"]

        it "doesn't let a static function used as a callback rely on its callers" $
            [ "void use(const uint8_t key[32]);"
            , "typedef int handler_cb(const uint8_t *data, uint16_t length);"
            , "void register_handler(handler_cb *cb);"
            , "static int helper(const uint8_t *data, uint16_t length) { use(data + 1); return 0; }"
            , "void init(void) { register_handler(helper); }"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past data + 1: has 0, 1..1"]

        it "doesn't let a static function rely on a length it changes" $
            [ "void use(const uint8_t key[32]);"
            , "static int helper(const uint8_t *data, uint16_t length) { length = 1; use(data + 1); return 0; }"
            , "int f(const uint8_t *data, uint16_t length) { return helper(data, length); }"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past data + 1: has 0, 1..1"]

        it "lets a function rely on its callers keeping a length small enough" $
            [ "typedef struct Chat { uint8_t name[48]; } Chat;"
            , "static void set_name(Chat *chat, const uint8_t *name, uint16_t name_length) { memcpy(chat->name, name, name_length); }"
            , "void f(Chat *chat, const uint8_t *name, uint16_t name_length) {"
            , "    if (name_length > 48) { return; }"
            , "    set_name(chat, name, name_length);"
            , "}"
            , "void g(Chat *chat, const uint8_t *name, uint16_t name_length) { set_name(chat, name, name_length); }"
            ] `shouldBeShort` ["set_name#3 at most 48, is 65535"]

        it "lets a static function rely on its callers relating its parameters" $
            [ "void use(const uint8_t *data, uint32_t length);"
            , "static void take(const uint8_t *packet, uint16_t length, uint16_t plain_size) { use(packet + 8, plain_size + 16); }"
            , "void f(const uint8_t *packet, uint16_t length) { if (length < 40) { return; } take(packet, length, length - 24); }"
            , "void g(const uint8_t *packet, uint16_t length) { if (length < 44) { return; } take(packet, length, 20); }"
            , "void h(const uint8_t *packet, uint16_t length) { take(packet, length, 20); }"
            ] `shouldBeShort` ["take 1*#2 -1*#3 -24, least -44"]

        it "knows what a function that returns true has checked of its parameters" $
            [ "void use(const uint8_t key[32]);"
            , "static bool check(const uint8_t *packet, uint16_t length) { if (length < 40) { return false; } return true; }"
            , "int f(const uint8_t *packet, uint16_t length) { if (!check(packet, length)) { return 1; } use(packet + 1); return 0; }"
            , "int g(const uint8_t *packet, uint16_t length) { if (check(packet, length)) { return 1; } use(packet + 1); return 0; }"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past packet + 1: has 0, 1..1"]

        it "passes a length that must be small enough up to the callers" $
            [ "typedef struct Chat { uint8_t name[48]; } Chat;"
            , "static void set_name(Chat *chat, const uint8_t *name, uint16_t name_length) { memcpy(chat->name, name, name_length); }"
            , "static void rename(Chat *chat, const uint8_t *name, uint16_t name_length) { set_name(chat, name, name_length); }"
            , "void f(Chat *chat, const uint8_t *name, uint16_t name_length) {"
            , "    if (name_length > 48) { return; }"
            , "    rename(chat, name, name_length);"
            , "}"
            , "void g(Chat *chat, const uint8_t *name, uint16_t name_length) { rename(chat, name, name_length); }"
            ] `shouldBeShort` ["rename#3 at most 48, is 65535"]

        it "lets a function rely on its callers keeping a count it goes on with small enough" $
            [ "typedef struct Node { uint8_t key[32]; } Node;"
            , "static bool has(const Node *nodes, uint32_t length, const uint8_t key[32]) {"
            , "    for (uint32_t i = 0; i < length; ++i) { if (nodes[i].key[0] == key[0]) { return true; } }"
            , "    return false;"
            , "}"
            , "static void fill(Node nodes[4], uint32_t *count_ptr, const Node from[8]) {"
            , "    uint32_t count = *count_ptr;"
            , "    for (uint32_t i = 0; i < 8; ++i) {"
            , "        if (has(nodes, count, from[i].key)) { continue; }"
            , "        if (count < 4) { nodes[count] = from[i]; ++count; }"
            , "    }"
            , "    *count_ptr = count;"
            , "}"
            , "int32_t f(Node nodes[4], const Node a[8], const Node b[8]) {"
            , "    uint32_t count = 0;"
            , "    fill(nodes, &count, a);"
            , "    fill(nodes, &count, b);"
            , "    return count;"
            , "}"
            , "void g(Node nodes[4], const Node a[8], uint32_t count) { fill(nodes, &count, a); }"
            ] `shouldBeShort` ["fill#2 points to at most 4, is 4294967295"]

        it "doesn't ask callers to keep a count small for a buffer whose size isn't fixed" $
            [ "typedef struct Node { uint8_t key[32]; } Node;"
            , "static void fill(Node *nodes, uint32_t *count_ptr, const Node from[8]) {"
            , "    uint32_t count = *count_ptr;"
            , "    for (uint32_t i = 0; i < 8; ++i) {"
            , "        if (count < 4) { nodes[count] = from[i]; ++count; }"
            , "    }"
            , "    *count_ptr = count;"
            , "}"
            , "void f(Node nodes[4], const Node a[8], uint32_t count) { fill(nodes, &count, a); }"
            ] `shouldBeShort` ["index nodes[count]: has 1, 0..3"]

    describe "what calls return at most" $ do
        it "knows the least of two numbers is at most a field it's given" $
            [ "typedef struct Table { uint16_t num_friends; } Table;"
            , "uint32_t min_u32(uint32_t a, uint32_t b) { return a < b ? a : b; }"
            , "uint32_t f(const Table *t) { const uint32_t m = min_u32(2, t->num_friends); assert(m <= t->num_friends); return m; }"
            ] `shouldBeShort` []

    describe "memory that starts as zeros" $ do
        let server alloc =
                [ "typedef struct Server { uint8_t *socks; uint32_t num_socks; } Server;"
                , "Server *make(uint32_t n) {"
                , "    Server *s = (Server *)" <> alloc <> ";"
                , "    if (s == nullptr) { return nullptr; }"
                , "    uint8_t *socks = (uint8_t *)malloc(n);"
                , "    if (socks == nullptr) { free(s); return nullptr; }"
                , "    s->socks = socks;"
                , "    return s;"
                , "}"
                ]
        it "knows the fields of what calloc gives start at 0" $
            server "calloc(1, sizeof(Server))" `shouldBeShort` []

        it "knows the fields of what a function that sets all it allocates to zeros gives start at 0" $
            ([ "void *zalloc(uint32_t size) {"
             , "    uint8_t *const ptr = (uint8_t *)malloc(size);"
             , "    if (ptr != nullptr) { memset(ptr, 0, size); }"
             , "    return ptr;"
             , "}"
             ] ++ server "zalloc(sizeof(Server))") `shouldBeShort` []

        it "doesn't take memory only partly set to zeros to start at 0" $
            ([ "void *zalloc(uint32_t size) {"
             , "    uint8_t *const ptr = (uint8_t *)malloc(size);"
             , "    if (ptr != nullptr) { memset(ptr, 0, 1); }"
             , "    return ptr;"
             , "}"
             ] ++ server "zalloc(sizeof(Server))") `shouldBeShort` ["s->socks vs s->num_socks: has 0, up to 4294967295"]

    describe "structs set to zeros" $ do
        let group =
                [ "typedef struct Group { uint8_t *items; uint32_t num_items; } Group;"
                , "static const Group empty_group = {0};"
                ]
        it "knows the fields of a struct given a constant of zeros are 0" $
            (group ++
            [ "uint8_t f(Group *g) { *g = empty_group; const uint8_t buf[4] = {0}; return buf[g->num_items]; }"
            ]) `shouldBeShort` []

        it "knows what a function leaves the fields it's given a pointer to at" $
            (group ++
            [ "static void setup(Group *g) { *g = empty_group; }"
            , "uint8_t f(Group *g) { setup(g); const uint8_t buf[4] = {0}; return buf[g->num_items]; }"
            ]) `shouldBeShort` []

        it "doesn't take what a call made only on one side of a condition leaves" $
            (group ++
            [ "static bool setup(Group *g) { *g = empty_group; return true; }"
            , "uint8_t f(Group *g, bool b) { if (b && setup(g)) { return 0; } const uint8_t buf[4] = {0}; return buf[g->num_items]; }"
            ]) `shouldBeShort` ["index buf[g->num_items]: has 4, 0..4294967295"]

    describe "buffers made through an address" $ do
        it "knows how many elements a call made a field have through its address" $
            [ "typedef struct Conn { uint8_t status; } Conn;"
            , "typedef struct Table { Conn *conns; uint32_t conns_count; } Table;"
            , "static int resize(Conn **array, size_t num) {"
            , "    if (num == 0) { free(*array); *array = nullptr; return 0; }"
            , "    Conn *temp = (Conn *)realloc(*array, num * sizeof(Conn));"
            , "    if (temp == nullptr) { return -1; }"
            , "    *array = temp;"
            , "    return 0;"
            , "}"
            , "uint8_t set(uint32_t n) {"
            , "    Table t = {nullptr, 0};"
            , "    if (n == 0 || resize(&t.conns, n) != 0) { return 0; }"
            , "    t.conns[n - 1].status = 1;"
            , "    const uint8_t status = t.conns[0].status;"
            , "    free(t.conns);"
            , "    return status;"
            , "}"
            ] `shouldBeShort` []

    describe "counts taken up that may wrap round" $ do
        it "keeps a buffer at least as long as a count that may wrap when it's taken up" $
            [ "typedef struct Table { uint8_t *data; uint16_t data_length; } Table;"
            , "int add(Table *t) {"
            , "    uint8_t *const temp = (uint8_t *)realloc(t->data, t->data_length + 1);"
            , "    if (temp == nullptr) { return -1; }"
            , "    t->data = temp;"
            , "    t->data[t->data_length] = 0;"
            , "    ++t->data_length;"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "keeps what's known through a copy of a count that may wrap when it's taken up" $
            [ "typedef struct Table { uint8_t *data; uint16_t data_length; } Table;"
            , "int add(Table *t) {"
            , "    uint8_t *const temp = (uint8_t *)realloc(t->data, t->data_length + 1);"
            , "    if (temp == nullptr) { return -1; }"
            , "    t->data = temp;"
            , "    const uint16_t id = t->data_length;"
            , "    ++t->data_length;"
            , "    t->data[id] = 0;"
            , "    return id;"
            , "}"
            ] `shouldBeShort` []

        it "doesn't keep what a count that may wrap was at least" $
            [ "uint8_t g(uint16_t n) {"
            , "    const uint8_t d[65536] = {0};"
            , "    if (n < 1) { return 0; }"
            , "    ++n;"
            , "    return d[n - 1];"
            , "}"
            ] `shouldBeShort` ["index d[n - 1]: has 65536, -1..65534"]

    describe "what static functions are given" $ do
        it "knows what all callers of a static function give it" $
            [ "static int32_t scaled(int32_t n) { return n * 1000; }"
            , "int32_t f(uint8_t x) { return scaled(x); }"
            , "int32_t g(void) { return scaled(2000); }"
            ] `shouldBeShort` []

        it "takes the most any caller gives" $
            [ "static int32_t scaled(int32_t n) { return n * 1000; }"
            , "int32_t f(uint8_t x) { return scaled(x); }"
            , "int32_t g(uint32_t x) { if (x > 3000000) { return 0; } return scaled(x); }"
            ] `shouldBeShort` ["overflow 0..3000000000"]

        it "knows what a static function's static callers are given" $
            [ "static int32_t scaled(int32_t n) { return n * 1000; }"
            , "static int32_t middle(int32_t n) { return scaled(n + 1); }"
            , "int32_t f(uint8_t x) { return middle(x); }"
            ] `shouldBeShort` []

        it "doesn't take what callers give a function others may call" $
            [ "int32_t scaled(int32_t n) { return n * 1000; }"
            , "int32_t f(uint8_t x) { return scaled(x); }"
            ] `shouldBeShort` ["overflow -2147483648000..2147483647000"]

        it "doesn't take what callers give a static function used as a value" $
            [ "typedef int32_t scale_cb(int32_t n);"
            , "void register_scale(scale_cb *cb);"
            , "static int32_t scaled(int32_t n) { return n * 1000; }"
            , "int32_t f(uint8_t x) { register_scale(scaled); return scaled(x); }"
            ] `shouldBeShort` ["overflow -2147483648000..2147483647000"]

        it "doesn't take what callers give a static function a macro calls" $
            [ "static int32_t scaled(int32_t n) { return n * 1000; }"
            , "#define SCALED(n) scaled(n)"
            , "int32_t f(uint8_t x) { return scaled(x); }"
            ] `shouldBeShort` ["overflow -2147483648000..2147483647000"]

    describe "lengths passed with buffers" $ do
        let useDecl = "void use(const uint8_t *data, uint16_t length);"
        it "reports a buffer shorter than the length passed with it" $
            [ useDecl
            , "void f(void) { uint8_t buf[16]; use(buf, 32); }"
            ] `shouldBeShort` ["use#1 vs #2: has 16, up to 32"]

        it "accepts a buffer passed with its size" $
            [ useDecl
            , "void f(void) { uint8_t buf[16]; use(buf, sizeof(buf)); }"
            ] `shouldBeShort` []

        it "accepts the rest of a buffer passed with what's left of its length" $
            [ useDecl
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    if (length < 1) { return -1; }"
            , "    use(data + 1, length - 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "follows a length given itself less something, like -=" $
            [ useDecl
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    if (length <= 33) { return -1; }"
            , "    const uint8_t *payload = data + 1;"
            , "    uint16_t payload_len = length - 1;"
            , "    payload_len = payload_len - 32;"
            , "    payload = payload + 32;"
            , "    use(payload, payload_len);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "checks a call with what's known where it's made" $
            [ "bool eq(const uint8_t *a, size_t a_size, const uint8_t *b, size_t b_size) { return a_size == b_size && memcmp(a, b, a_size) == 0; }"
            , "bool f(const uint8_t *a, size_t a_size, const uint8_t *b, size_t b_size) { return a_size != b_size || memcmp(a, b, a_size) == 0; }"
            , "bool g(const uint8_t *a, size_t a_size, const uint8_t *b, size_t b_size) { return a_size <= b_size ? memcmp(a, b, a_size) == 0 : false; }"
            ] `shouldBeShort` []

        it "accepts a buffer and its length passed on" $
            [ useDecl
            , "void f(const uint8_t *data, uint16_t length) { use(data, length); }"
            ] `shouldBeShort` []

        it "reports a length that isn't known to fit the buffer" $
            [ useDecl
            , "void f(uint16_t n) { uint8_t buf[16]; use(buf, n); }"
            ] `shouldBeShort` ["use#1 vs #2: has 16, up to 65535"]

        it "accepts a length made smaller by an unsigned type" $
            [ useDecl
            , "void f(const uint8_t *data, size_t length) { use(data, length); }"
            , "void g(const uint8_t *data, size_t length) { const uint16_t n = length; use(data, n); }"
            ] `shouldBeShort` []

        it "knows the range of a shift" $
            [ useDecl
            , "void f(uint32_t n) { uint8_t buf[16]; if (n > 4) { return; } use(buf, 1 << n); }"
            , "void g(uint16_t n) { uint8_t buf[16]; use(buf, n >> 12); }"
            , "void h(uint32_t n) { uint8_t buf[16]; if (n > 5) { return; } use(buf, 1 << n); }"
            ] `shouldBeShort` ["use#1 vs #2: has 16, up to 32"]

        it "doesn't pair a length with a pointer named as one value" $
            [ "bool read_max(uint8_t data[48], uint16_t *data_length_ptr, uint16_t max_data_length);"
            , "void f(void) { uint8_t buf[48]; uint16_t len; read_max(buf, &len, sizeof(buf)); }"
            ] `shouldBeShort` []

        it "knows a number equal to a size it's compared with as one" $
            [ useDecl
            , "int get(void);"
            , "void f(void) { uint8_t buf[64]; const int n = get(); if (n != sizeof(buf)) { return; } use(buf, n); }"
            ] `shouldBeShort` []

        it "doesn't take numbers equal as unsigned to be equal" $
            [ useDecl
            , "int get(void);"
            , "void f(unsigned int u) { uint8_t buf[64]; const int n = get(); if (n != u) { return; } use(buf, n); }"
            ] `shouldBeShort` ["use#1 vs #2: has 64, up to 65535", "unsigned n to uint16_t, least -2147483648"]

        it "accepts a length a function returns that's at most what it's given" $
            [ useDecl
            , "static int create(const uint8_t *plain, uint16_t plain_length, uint8_t *packet, uint16_t length) {"
            , "    if (length < plain_length + 1) { return -1; }"
            , "    packet[0] = 1;"
            , "    memcpy(packet + 1, plain, plain_length);"
            , "    return plain_length + 1;"
            , "}"
            , "void f(const uint8_t *plain, uint16_t plain_length) {"
            , "    uint8_t packet[64];"
            , "    const int len = create(plain, plain_length, packet, sizeof(packet));"
            , "    if (len == -1) { return; }"
            , "    use(packet, len);"
            , "}"
            ] `shouldBeShort` []

        it "accepts a length a function returns, at most a size it's given that its type holds" $
            [ useDecl
            , "int32_t check(size_t length, uint16_t stored) { if (stored > length) { return -1; } return stored; }"
            , "void f(uint16_t stored) { uint8_t buf[64]; const int32_t n = check(sizeof(buf), stored); if (n == -1) { return; } use(buf, n); }"
            ] `shouldBeShort` []

        it "doesn't take a function to fail only with what it returns below 0 on purpose" $
            [ useDecl
            , "int32_t check(size_t length, uint16_t stored, int32_t other) { if (stored > length) { return other; } return stored; }"
            , "void f(uint16_t stored, int32_t other) { uint8_t buf[64]; const int32_t n = check(sizeof(buf), stored, other); if (n == -1) { return; } use(buf, n); }"
            ] `shouldBeShort` ["use#1 vs #2: has 64, up to 65535", "unsigned n to uint16_t, least -2147483648"]

        it "accepts the smaller of 2 lengths" $
            [ "uint16_t min_u16(uint16_t a, uint16_t b) { return a < b ? a : b; }"
            , "void f(const uint8_t *data, uint16_t length) { uint8_t buf[16]; memcpy(buf, data, min_u16(length, sizeof(buf))); }"
            ] `shouldBeShort` []

        it "reports a length a function returns that's more than what it's given" $
            [ useDecl
            , "static int more(uint16_t length) { return length + 1; }"
            , "void f(const uint8_t *data, uint16_t length) { use(data, more(length)); }"
            ] `shouldBeShort` ["use#1 vs #2: has 0, up to 65535"]

        it "reports a length that wraps from below 0" $
            [ useDecl
            , "void f(const uint8_t *data, size_t length) { use(data, length - 1); }"
            ] `shouldBeShort` ["use#1 vs #2: has 0, up to 65535"]

    describe "counts passed with arrays" $ do
        it "doesn't take a length after an array of a fixed size as its size" $
            [ "static bool check(const uint8_t password[32], const uint8_t stored[32], uint16_t length) {"
            , "    if (length > 32) { return false; }"
            , "    return memcmp(stored, password, length) == 0;"
            , "}"
            , "bool f(const uint8_t *data, uint16_t data_length, const uint8_t stored[32]) {"
            , "    if (data_length < 36) { return false; }"
            , "    uint16_t length;"
            , "    net_unpack_u16(data, &length);"
            , "    return check(data + 4, stored, length);"
            , "}"
            ] `shouldBeShort` []

        it "pairs an array with the most it may hold wherever that comes" $
            [ "typedef struct Entry { uint8_t type; } Entry;"
            , "static uint32_t fill(Entry entries[], const uint8_t *flags, uint32_t max_entries, uint32_t n) {"
            , "    uint32_t count = 0;"
            , "    for (uint32_t i = 0; i < n && count < max_entries; ++i) { entries[count].type = flags[0]; ++count; }"
            , "    return count;"
            , "}"
            , "uint32_t f(const uint8_t flags[1]) { Entry e[4]; return fill(e, flags, 4, 9); }"
            ] `shouldBeShort` []

        it "pairs an array with the most it may hold after it" $
            [ "static uint32_t fill(uint32_t results[], uint32_t max_results, uint32_t n) {"
            , "    uint32_t count = 0;"
            , "    for (uint32_t i = 0; i < n && count < max_results; ++i) { results[count] = i; ++count; }"
            , "    return count;"
            , "}"
            , "uint32_t f(void) { uint32_t r[4]; return fill(r, 4, 9); }"
            , "uint32_t g(void) { uint32_t r[4]; return fill(r, 8, 9); }"
            ] `shouldBeShort` ["fill#1 vs #2: has 4, up to 8"]

        let items =
                [ "typedef struct Item { uint8_t key[32]; uint32_t n; } Item;"
                , "void use_items(const Item *items, uint16_t num_items);"
                , "void use_counted(const Item *items, uint16_t items_count);"
                ]
        it "reports an array with fewer elements than the count passed with it" $
            (items ++
            [ "void f(void) { Item items[4]; use_items(items, 8); use_counted(items, 8); }"
            ]) `shouldBeShort` ["use_items#1 vs #2: has 4, up to 8", "use_counted#1 vs #2: has 4, up to 8"]

        it "accepts an array and its count passed on, from parameters or fields" $
            (items ++
            [ "typedef struct List { Item *items; uint16_t num_items; } List;"
            , "void f(const Item *items, uint16_t num_items) { use_items(items, num_items); }"
            , "void g(const List *list) { use_items(list->items, list->num_items); }"
            ]) `shouldBeShort` []

        it "doesn't take a bare size next to a pointer to a struct as its count" $
            [ "typedef struct Node { struct Node *next; uint16_t size; } Node;"
            , "void f(Node *n, Node *m) { n->next = m; }"
            ] `shouldBeShort` []

        it "doesn't take a count of what isn't known as bytes" $
            [ "void use_any(const void *arr, uint32_t arr_count);"
            , "void f(void) { uint8_t buf[4]; use_any(buf, 8); }"
            ] `shouldBeShort` []

    describe "arrays with room for more than they hold" $ do
        let list =
                [ "typedef struct Memory Memory;"
                , "GNU_ALLOC_SIZE(3, 4) void *mem_vrealloc(const Memory *mem, void *ptr, uint32_t nmemb, uint32_t size);"
                , "void *mem_vrealloc(const Memory *mem, void *ptr, uint32_t nmemb, uint32_t size) { return realloc(ptr, nmemb * size); }"
                , "typedef struct Item { int x; } Item;"
                , "typedef struct List { const Memory *mem; Item *items; uint32_t items_count; uint32_t items_capacity; } List;"
                , "bool add(List *l, int x) {"
                , "  if (l->items_count == l->items_capacity) {"
                , "    if (l->items_capacity >= 1000) { return false; }"
                , "    const uint32_t new_capacity = l->items_capacity + 8;"
                , "    Item *tmp = (Item *)mem_vrealloc(l->mem, l->items, new_capacity, sizeof(Item));"
                , "    if (tmp == nullptr) { return false; }"
                , "    l->items = tmp;"
                , "    l->items_capacity = new_capacity;"
                , "  }"
                , "  l->items[l->items_count].x = x;"
                , "  ++l->items_count;"
                , "  return true;"
                , "}"
                , "int get(const List *l, uint32_t i) { if (i >= l->items_count) { return 0; } return l->items[i].x; }"
                ]
        it "knows an array has room for its capacity, and holds at most that many" $
            list `shouldBeShort` []

        it "reports a count that may grow past the capacity" $
            (list ++
            [ "void grow(List *l) { ++l->items_count; }"
            ]) `shouldBeShort` ["l->items_count over l->items_capacity"]

        it "reports a capacity that may shrink below the count" $
            (list ++
            [ "void shrink(List *l) { l->items_capacity = 0; }"
            ]) `shouldBeShort` ["l->items_count over l->items_capacity"]

        let push =
                [ "bool push(List *l, int x) {"
                , "  if (l->items_count >= 1000) { return false; }"
                , "  if (reserve(l, l->items_count + 1) == -1) { return false; }"
                , "  l->items[l->items_count].x = x;"
                , "  ++l->items_count;"
                , "  return true;"
                , "}"
                ]
        it "knows what a function has made sure of where it says it did" $
            (list ++
            [ "static int reserve(List *l, uint32_t num) {"
            , "  if (num <= l->items_capacity) { return 0; }"
            , "  Item *tmp = (Item *)mem_vrealloc(l->mem, l->items, num, sizeof(Item));"
            , "  if (tmp == nullptr) { return -1; }"
            , "  l->items = tmp;"
            , "  l->items_capacity = num;"
            , "  return 0;"
            , "}"
            ] ++ push) `shouldBeShort` []

        it "doesn't take a function to have made sure of what it hasn't everywhere it says it did" $
            (list ++
            [ "static int reserve(List *l, uint32_t num) {"
            , "  if (num > 2000) { return 0; }"
            , "  Item *tmp = (Item *)mem_vrealloc(l->mem, l->items, num, sizeof(Item));"
            , "  if (tmp == nullptr) { return -1; }"
            , "  l->items = tmp;"
            , "  l->items_capacity = num;"
            , "  return 0;"
            , "}"
            ] ++ push) `shouldBeShort` ["index l->items[l->items_count]: has 0, 0..999", "l->items_count over l->items_capacity"]

    describe "what fields are given" $ do
        let item =
                [ "typedef struct Item { uint16_t n; } Item;"
                , "void use(const uint8_t *data, uint16_t length);"
                , "void set(Item *it, uint16_t v) { if (v > 16) { return; } it->n = v; }"
                , "void f(const Item *it) { uint8_t buf[16]; use(buf, it->n); }"
                ]
            unknown = ["use#1 vs #2: has 16, up to 65535"]
        it "knows a field is only ever given what's stored in it" $
            item `shouldBeShort` []

        it "knows how many elements a pointer field is given in an initialiser" $
            [ "typedef struct Cmp { int32_t n; const uint8_t *key; } Cmp;"
            , "void use(const uint8_t key[32]);"
            , "static void compare(const Cmp *cmp) { use(cmp->key); }"
            , "void f(const uint8_t key[32]) { const Cmp cmp = { 1, key }; compare(&cmp); }"
            , "void g(const uint8_t key[16]) { const Cmp cmp = { 2, key }; compare(&cmp); }"
            ] `shouldBeShort` ["use#1 needs 32, has 16"]

        it "knows a signed field only ever given numbers that aren't negative isn't" $
            [ "typedef struct Chat { int number; } Chat;"
            , "void use(uint32_t n);"
            , "void set(Chat *c, int n) { if (n < 0) { return; } c->number = n; }"
            , "void f(const Chat *c) { use(c->number); }"
            ] `shouldBeShort` []

        it "knows a count kept from growing too far" $
            [ "typedef struct List { uint32_t count; } List;"
            , "void use(const uint8_t *data, uint32_t length);"
            , "void add(List *l) { if (l->count >= 16) { return; } ++l->count; }"
            , "void f(const List *l) { uint8_t buf[16]; use(buf, l->count); }"
            ] `shouldBeShort` []

        it "knows a count taken down only when it isn't 0 stays in what it's given" $
            [ "typedef struct List { uint32_t count; } List;"
            , "void use(const uint8_t *data, uint32_t length);"
            , "void add(List *l) { if (l->count >= 16) { return; } ++l->count; }"
            , "void drop(List *l) { if (l->count == 0) { return; } --l->count; }"
            , "void f(const List *l) { uint8_t buf[16]; use(buf, l->count); }"
            ] `shouldBeShort` []

        it "keeps what's known of a count where another is given up on that many calls use" $
            ([ "typedef struct List { uint32_t count; uint32_t other; } List;"
             , "void use(const uint8_t *data, uint32_t length);"
             , "void add(List *l) { if (l->count >= 16) { return; } ++l->count; }"
             , "void drop(List *l) { if (l->count == 0) { return; } --l->count; }"
             , "void f(const List *l) { uint8_t buf[16]; use(buf, l->count); }"
             , "void more(List *l) { if (l->other >= 16) { return; } ++l->other; }"
             , "void less(List *l) { --l->other; }"
             , "static uint32_t get0(const List *l) { return l->other; }"
             ] ++
             [ "static uint32_t get" <> T.pack (show k) <> "(const List *l) { return get" <> T.pack (show (k - 1)) <> "(l); }" | k <- [1 .. 12 :: Int] ] ++
             [ "void h(const List *l) { uint8_t buf[16]; use(buf, get12(l)); }"
             ]) `shouldBeShort` ["use#1 vs #2: has 16, up to 4294967295"]

        it "doesn't take a count taken down past 0 as smaller" $
            [ "typedef struct List { uint32_t count; } List;"
            , "void use(const uint8_t *data, uint32_t length);"
            , "void add(List *l) { if (l->count >= 16) { return; } ++l->count; }"
            , "void drop(List *l) { --l->count; }"
            , "void f(const List *l) { uint8_t buf[16]; use(buf, l->count); }"
            ] `shouldBeShort` ["use#1 vs #2: has 16, up to 4294967295"]

        it "doesn't know a field given through its address" $
            (item ++
            [ "void read16(uint16_t *v);"
            , "void g(Item *it) { read16(&it->n); }"
            ]) `shouldBeShort` unknown

        it "doesn't know a field of a struct given bytes" $
            (item ++
            [ "void g(Item *it, const uint8_t data[8]) { memcpy(it, data, sizeof(Item)); }"
            ]) `shouldBeShort` unknown

        it "doesn't know a field of a struct passed on as something else" $
            (item ++
            [ "void fill(void *p, size_t n);"
            , "void g(Item *it) { fill(it, sizeof(Item)); }"
            ]) `shouldBeShort` unknown

        it "doesn't know a field of a struct a function gives bytes through what it's given" $
            (item ++
            [ "static void fill(void *p, size_t n) { memset(p, 0xff, n); }"
            , "void g(Item *it) { fill(it, sizeof(Item)); }"
            ]) `shouldBeShort` unknown

        it "doesn't know a field of a struct a function stores bytes in" $
            (item ++
            [ "static void poke(uint8_t *p) { p[0] = 0xff; }"
            , "void g(Item *it) { poke((uint8_t *)it); }"
            ]) `shouldBeShort` unknown

        it "doesn't know a field of a struct converted to bytes elsewhere" $
            (item ++
            [ "void g(Item *it) { uint8_t *b = (uint8_t *)it; b[0] = 0xff; }"
            ]) `shouldBeShort` unknown

        it "doesn't know a field of a struct a function stores bytes in through its own pointer" $
            (item ++
            [ "static void poke(void *p) { uint8_t *b = (uint8_t *)p; b[0] = 0xff; }"
            , "void g(Item *it) { poke(it); }"
            ]) `shouldBeShort` unknown

        it "knows a field of a struct kept as a callback's object" $
            (item ++
            [ "static void *kept = nullptr;"
            , "static void keep(void *object) { kept = object; }"
            , "void g(Item *it) { keep(it); }"
            ]) `shouldBeShort` []

        it "doesn't know a field of a struct kept for a callback that writes bytes through it" $
            (item ++
            [ "typedef void object_cb(void *object);"
            , "typedef struct Later { object_cb *cb; void *object; } Later;"
            , "static void wipe(void *object) { memset(object, 0xff, 1); }"
            , "void later(Later *l, Item *it) { l->cb = &wipe; l->object = it; }"
            , "void fire(const Later *l) { l->cb(l->object); }"
            ]) `shouldBeShort` unknown

        it "knows a field of a struct wiped with zeros" $
            (item ++
            [ "void g(Item *it) { memset(it, 0, sizeof(Item)); }"
            ]) `shouldBeShort` []

        it "knows a field of a struct copied whole through what a function is given" $
            (item ++
            [ "static void set_at(void *arr, const Item *v) { Item *dst = (Item *)arr; *dst = *v; }"
            , "void g(Item *items, const Item *v) { set_at(items, v); }"
            ]) `shouldBeShort` []

        it "knows a field of a struct only given to a function that frees it" $
            (item ++
            [ "static void release(void *p) { free(p); }"
            , "void g(Item *it) { release(it); }"
            ]) `shouldBeShort` []

        it "doesn't know a field of a struct inside one given bytes" $
            (item ++
            [ "typedef struct Outer { Item item; } Outer;"
            , "void g(Outer *o, const uint8_t data[8]) { memcpy(o, data, sizeof(Outer)); }"
            ]) `shouldBeShort` unknown

        it "doesn't know a field of a struct in a union" $
            (item ++
            [ "typedef union Both { Item item; uint32_t word; } Both;"
            ]) `shouldBeShort` unknown

        it "doesn't know a field initialised with something else" $
            (item ++
            [ "static const Item big = {100};"
            , "void g(Item *it) { *it = big; }"
            ]) `shouldBeShort` unknown

        it "knows a field of a struct initialised with zeros" $
            (item ++
            [ "void g(void) { Item it = {0}; set(&it, 3); }"
            ]) `shouldBeShort` []

    describe "fields with lengths" $ do
        let decls =
                [ "void use(const uint8_t *data, uint16_t length);"
                , "void use_key(const uint8_t key[32]);"
                , "typedef struct Event { uint8_t *data; uint16_t data_length; } Event;"
                , "typedef struct Name { uint16_t name_length; uint8_t name[16]; } Name;"
                , "typedef struct Packet { uint8_t *data; uint16_t length; } Packet;"
                ]
            allocator = "GNU_ALLOC_SIZE(2) void *mem_balloc(const Memory *mem, uint32_t size);"
            unpack =
                [ "typedef struct State { uint8_t name[48]; uint16_t name_len; } State;"
                , "bool read_size(uint32_t *size);"
                , "bool unpack_max(uint8_t *data, uint16_t max_data_length, uint16_t *data_length_ptr) {"
                , "    uint32_t size;"
                , "    if (!read_size(&size) || size > max_data_length) { return false; }"
                , "    *data_length_ptr = size;"
                , "    return true;"
                , "}"
                ]
        it "trusts a buffer field and its length field where they're read" $
            (decls ++
            [ "void f(const Event *e) { use(e->data, e->data_length); }"
            ]) `shouldBeShort` []

        it "trusts an array field and its length field where they're read" $
            (decls ++
            [ "void f(const Name *n) { use(n->name, n->name_length); }"
            ]) `shouldBeShort` []

        it "pairs a length called length with the buffer next to it" $
            (decls ++
            [ "typedef struct Apart { uint8_t *data; uint32_t id; uint16_t length; } Apart;"
            , "void f(const Packet *p, const Apart *a) { use(p->data, p->length); use(a->data, a->length); }"
            ]) `shouldBeShort` ["use#1 vs #2: unknown, up to 65535"]

        it "accepts a buffer stored with its length, in either order" $
            (decls ++
            [ "void f(Event *e, Event *g, uint8_t *data, uint16_t length) {"
            , "    e->data = data;"
            , "    e->data_length = length;"
            , "    g->data_length = length;"
            , "    g->data = data;"
            , "}"
            ]) `shouldBeShort` []

        it "reports a buffer stored with a length it doesn't have" $
            (decls ++
            [ "void f(Event *e, uint8_t buf[16]) {"
            , "    e->data = buf;"
            , "    e->data_length = 32;"
            , "}"
            ]) `shouldBeShort` ["e->data vs e->data_length: has 16, up to 32"]

        it "reports a length stored that its array doesn't have" $
            (decls ++
            [ "void f(Name *n, uint16_t length) { n->name_length = length; }"
            , "int g(Name *n, uint16_t length) {"
            , "    if (length > sizeof(n->name)) { return -1; }"
            , "    n->name_length = length;"
            , "    return 0;"
            , "}"
            ]) `shouldBeShort` ["n->name vs n->name_length: has 16, up to 65535"]

        it "accepts a buffer emptied with nullptr" $
            (decls ++
            [ "void f(Event *e, uint8_t *data, uint16_t length) {"
            , "    if (e->data != nullptr) {"
            , "        e->data = nullptr;"
            , "        e->data_length = 0;"
            , "    }"
            , "    if (length == 0) { return; }"
            , "    e->data = data;"
            , "    e->data_length = length;"
            , "}"
            ]) `shouldBeShort` []

        it "checks a pair where a call can see it" $
            (decls ++
            [ "void g(Event *e);"
            , "void f(Event *e, uint8_t buf[16]) {"
            , "    e->data = buf;"
            , "    g(e);"
            , "}"
            ]) `shouldBeShort` ["e->data vs e->data_length: has 16, up to 65535"]

        it "doesn't check a pair at a call that is only given the buffer" $
            (decls ++
            [ "void f(Event *e, uint8_t buf[16]) {"
            , "    e->data = buf;"
            , "    fill(e->data);"
            , "    e->data_length = 16;"
            , "}"
            ]) `shouldBeShort` []

        it "keeps what's known of a length across a call that only stores its buffer" $
            (decls ++
            [ "void set(Event *e, uint8_t buf[65535]) { e->data = buf; }"
            , "void f(Event *e, uint8_t buf[65535]) {"
            , "    if (e->data_length > 16) { return; }"
            , "    set(e, buf);"
            , "    uint8_t copy[16];"
            , "    use(copy, e->data_length);"
            , "}"
            ]) `shouldBeShort` []

        it "checks a local struct's pair where it's passed" $
            (decls ++
            [ "void send(const Packet *p);"
            , "void f(uint8_t buf[16]) {"
            , "    Packet p;"
            , "    p.data = buf;"
            , "    p.length = 32;"
            , "    send(&p);"
            , "}"
            ]) `shouldBeShort` ["p.data vs p.length: has 16, up to 32"]

        it "reports a length field read by a call until it's checked" $
            (decls ++
            [ "void read_u16(uint16_t *value);"
            , "void f(Name *n) { read_u16(&n->name_length); }"
            , "void g(Name *n) {"
            , "    read_u16(&n->name_length);"
            , "    if (n->name_length > 16) { n->name_length = 16; }"
            , "}"
            ]) `shouldBeShort` ["n->name vs n->name_length: has 16, up to 65535"]

        it "trusts what out-parameters for a buffer and its length are given" $
            (decls ++
            [ "typedef struct Event32 { uint8_t *data; uint32_t data_length; } Event32;"
            , "bool unpack(uint8_t **data_ptr, uint32_t *data_length_ptr);"
            , "bool f(Event32 *e) { return unpack(&e->data, &e->data_length); }"
            ]) `shouldBeShort` []

        it "checks what out-parameters for a buffer and its length are given" $
            (decls ++
            [ "bool unpack(uint8_t **data_ptr, uint32_t *data_length_ptr, uint8_t buf[16]) {"
            , "    *data_ptr = buf;"
            , "    *data_length_ptr = 32;"
            , "    return true;"
            , "}"
            ]) `shouldBeShort` ["*data_ptr vs *data_length_ptr: has 16, up to 32"]

        it "follows a field through a guard" $
            (decls ++
            [ "int f(const Packet *p) {"
            , "    if (p->length < 33) { return -1; }"
            , "    use_key(p->data + 1);"
            , "    return 0;"
            , "}"
            ]) `shouldBeShort` []

        it "forgets what a call can change" $
            (decls ++
            [ "void g(Packet *p);"
            , "int f(Packet *p) {"
            , "    if (p->length < 33) { return -1; }"
            , "    g(p);"
            , "    use_key(p->data + 1);"
            , "    return 0;"
            , "}"
            ]) `shouldBeShort` ["use_key#1 needs 32, has 0", "past p->data + 1: has 0, 1..1"]

        it "keeps a buffer with its length where branches meet" $
            (decls ++
            [ allocator
            , "bool f(Event *e, const Memory *mem, const uint8_t *data, uint16_t length) {"
            , "    if (length == 0) {"
            , "        e->data = nullptr;"
            , "        e->data_length = 0;"
            , "    } else {"
            , "        uint8_t *copy = (uint8_t *)mem_balloc(mem, length);"
            , "        if (copy == nullptr) { return false; }"
            , "        e->data = copy;"
            , "        e->data_length = length;"
            , "    }"
            , "    return true;"
            , "}"
            ]) `shouldBeShort` []

        it "keeps a length read by a call through stores of something else" $
            (decls ++
            [ allocator
            , "bool read_size(uint32_t *size);"
            , "bool f(const Memory *mem, uint8_t **data_ptr, uint32_t *data_length_ptr) {"
            , "    uint32_t size;"
            , "    if (!read_size(&size)) { return false; }"
            , "    uint8_t *const data = (uint8_t *)mem_balloc(mem, size);"
            , "    *data_ptr = data;"
            , "    *data_length_ptr = size;"
            , "    return true;"
            , "}"
            ]) `shouldBeShort` []

        it "doesn't trust a length a call is given a pointer to" $
            (decls ++
            [ "void read_u32(uint32_t *value);"
            , "bool f(uint8_t **data_ptr, uint32_t *data_length_ptr) { read_u32(data_length_ptr); return true; }"
            ]) `shouldBeShort` ["*data_ptr vs *data_length_ptr: has 0, up to 4294967295"]

        it "takes what's read off a buffer from its length" $
            (decls ++
            [ "typedef struct Reader { const uint8_t *bytes; uint32_t bytes_size; } Reader;"
            , "bool f(Reader *r, uint8_t *out, size_t limit) {"
            , "    if (limit > r->bytes_size) { return false; }"
            , "    r->bytes += limit;"
            , "    r->bytes_size -= limit;"
            , "    return true;"
            , "}"
            ]) `shouldBeShort` []

        it "takes one more than a length that isn't the most there is" $
            (decls ++
            [ allocator
            , "typedef struct Text { char *text; uint32_t text_length; } Text;"
            , "bool f(Text *t, const Memory *mem, uint32_t length) {"
            , "    if (length == UINT32_MAX) { return false; }"
            , "    char *copy = (char *)mem_balloc(mem, length + 1);"
            , "    if (copy == nullptr) { return false; }"
            , "    t->text = copy;"
            , "    t->text_length = length;"
            , "    return true;"
            , "}"
            ]) `shouldBeShort` []

        it "lets a call fill in a local struct" $
            (decls ++
            [ "void fill(Packet *p);"
            , "void send(const Packet *p);"
            , "void f(void) { Packet p; fill(&p); send(&p); }"
            ]) `shouldBeShort` []

        it "reports a length changed in a loop" $
            (decls ++
            [ "void f(Packet *p) { while (p->length < 100) { ++p->length; } }"
            ]) `shouldBeShort` ["p->data vs p->length: unknown, up to 65535"]

        it "knows what a call stores through a pointer it's given" $
            (unpack ++
            [ "bool load(State *s) {"
            , "    if (!unpack_max(s->name, sizeof(s->name), &s->name_len)) { return false; }"
            , "    return true;"
            , "}"
            ]) `shouldBeShort` []

        it "knows what a call stored through a pointer where it says it succeeded" $
            [ "typedef struct Node { uint8_t key[32]; } Node;"
            , "void use(const Node *node);"
            , "static bool fetch(uint32_t size, uint32_t *count_out) { if (size > 4) { return false; } *count_out = size; return true; }"
            , "static bool maybe(uint32_t size, uint32_t *count_out) { if (size > 4) { return true; } *count_out = size; return true; }"
            , "int f(uint32_t size) {"
            , "    Node nodes[4] = {{{0}}};"
            , "    uint32_t count;"
            , "    if (!fetch(size, &count)) { return 1; }"
            , "    for (uint32_t i = 0; i < count; ++i) { use(&nodes[i]); }"
            , "    return 0;"
            , "}"
            , "int g(uint32_t size) {"
            , "    Node nodes[4] = {{{0}}};"
            , "    uint32_t count;"
            , "    if (!maybe(size, &count)) { return 1; }"
            , "    for (uint32_t i = 0; i < count; ++i) { use(&nodes[i]); }"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["index nodes[i]: has 4, 0..4294967294"]

        it "doesn't know what's stored where another call may store too" $
            (unpack ++
            [ "bool unpack_u16(uint16_t *val);"
            , "bool load(State *s) {"
            , "    if (!(unpack_u16(&s->name_len) && unpack_max(s->name, sizeof(s->name), &s->name_len))) { return false; }"
            , "    return true;"
            , "}"
            ]) `shouldBeShort` ["s->name vs s->name_len: has 48, up to 65535", "s->name vs s->name_len: has 48, up to 65535"]

        it "doesn't know what's stored by a call that does more with the pointer" $
            (unpack ++
            [ "void keep(uint16_t *p);"
            , "bool unpack_keep(uint16_t *data_length_ptr) { *data_length_ptr = 0; keep(data_length_ptr); return true; }"
            , "bool load(State *s) {"
            , "    if (!unpack_keep(&s->name_len)) { return false; }"
            , "    return true;"
            , "}"
            ]) `shouldBeShort` ["s->name vs s->name_len: has 48, up to 65535", "s->name vs s->name_len: has 48, up to 65535"]

        it "knows a string is shorter than what holds it" $
            [ "typedef struct Ip_Ntoa { char buf[96]; uint16_t length; } Ip_Ntoa;"
            , "void f(Ip_Ntoa *ip_str) {"
            , "    snprintf(ip_str->buf, sizeof(ip_str->buf), \"(none)\");"
            , "    ip_str->length = (uint16_t)strlen(ip_str->buf);"
            , "}"
            ] `shouldBeShort` []

        it "doesn't take an array parameter's size as the most its string has" $
            [ "typedef struct Ip_Ntoa { char buf[96]; uint16_t length; } Ip_Ntoa;"
            , "void f(Ip_Ntoa *ip_str, const char s[96]) {"
            , "    snprintf(ip_str->buf, sizeof(ip_str->buf), \"%s\", s);"
            , "    ip_str->length = (uint16_t)strlen(s);"
            , "}"
            ] `shouldBeShort` ["ip_str->buf vs ip_str->length: has 96, up to 65535"]

    describe "bytes" $ do
        let randomBytes = "void random_bytes(uint8_t *bytes, size_t length);"
        it "counts the bytes of a value seen as bytes" $
            [ randomBytes
            , "uint16_t f(void) { uint16_t r; random_bytes((uint8_t *)&r, sizeof(r)); return r; }"
            ] `shouldBeShort` []

        it "reports a value seen as more bytes than it has" $
            [ randomBytes
            , "uint16_t f(void) { uint16_t r; random_bytes((uint8_t *)&r, 4); return r; }"
            ] `shouldBeShort` ["random_bytes#1 vs #2: has 2, up to 4"]

        it "measures a void pointer and its length in bytes" $
            [ "void zero(void *data, size_t length);"
            , "void f(void) { uint32_t words[4]; zero(words, sizeof(words)); zero(words, 17); }"
            ] `shouldBeShort` ["zero#1 vs #2: has 16, up to 17"]

        it "checks what memcpy, memmove, memset and memcmp are given" $
            [ "void f(const uint8_t *src, uint16_t length) {"
            , "    uint8_t buf[16];"
            , "    memset(buf, 0, sizeof(buf));"
            , "    if (length <= sizeof(buf)) { memcpy(buf, src, length); }"
            , "    memmove(buf, buf + 1, 16);"
            , "    if (memcmp(buf, src, 20) == 0) { return; }"
            , "}"
            ] `shouldBeShort`
                [ "memmove#2 vs #3: has 15, up to 16"
                , "memcmp#1 vs #3: has 16, up to 20"
                , "memcmp#2 vs #3: has 0, up to 20"
                ]

        it "counts the bytes of structs by their size" $
            [ "typedef struct Pair { uint32_t a; uint8_t *b; } Pair;"
            , "void f(Pair *dst, const Pair *src, const Pair pairs[2]) {"
            , "    memcpy(dst, src, sizeof(Pair));"
            , "    memcpy(dst, pairs, 2 * sizeof(Pair));"
            , "}"
            ] `shouldBeShort` ["memcpy#1 vs #3: has 1, up to 2"]

        it "knows the most a struct's size can be" $
            [ "typedef union Ip4 { uint32_t uint32; uint8_t uint8[4]; } Ip4;"
            , "void use(const uint8_t *data, uint16_t length);"
            , "void f(void) { uint8_t buf[64]; uint16_t length = 2 + sizeof(Ip4); use(buf, length); }"
            ] `shouldBeShort` []

        it "bounds what's left of a division and a mask" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "void f(uint32_t n) { uint8_t buf[16]; use(buf, n % 16); use(buf, n & 15); use(buf, n % 18); }"
            ] `shouldBeShort` ["use#1 vs #2: has 16, up to 17"]

        it "checks each side of a choice of length" $
            [ "void f(const uint8_t *data, size_t length) {"
            , "    uint8_t out[16];"
            , "    memcpy(out, data, length < 16 ? length : 16);"
            , "    memcpy(out, data, length < 32 ? length : 32);"
            , "}"
            ] `shouldBeShort` ["memcpy#1 vs #3: has 16, up to 32"]

        it "knows a variable an unknown call fills in holds what its type does" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "bool read_size(uint32_t *size);"
            , "void f(void) { uint8_t buf[48]; uint32_t size; if (!read_size(&size) || size > 48) { return; } use(buf, size); }"
            ] `shouldBeShort` []

        it "knows a choice is at least what each side is" $
            [ "void f(uint8_t *packet, uint16_t packet_size, const uint8_t *data, uint16_t length, bool lossless) {"
            , "    const uint32_t needed = lossless ? length + 9 : length + 1;"
            , "    if (needed > packet_size) { return; }"
            , "    memcpy(packet + 1, data, length);"
            , "}"
            , "void g(uint8_t *packet, uint16_t packet_size, const uint8_t *data, uint16_t length, bool lossless) {"
            , "    const uint32_t needed = lossless ? length + 9 : length;"
            , "    if (needed > packet_size) { return; }"
            , "    memcpy(packet + 1, data, length);"
            , "}"
            ] `shouldBeShort` ["memcpy#1 vs #3: has 0, up to 65535", "past packet + 1: has 0, 1..1"]

        it "knows a variable is the sum it was given" $
            [ "void use(const uint8_t *data, uint32_t length);"
            , "void f(uint8_t *packet, uint16_t packet_size, uint16_t a, uint16_t b, bool c) {"
            , "    const uint32_t needed = c ? a + b + 9 : a + b + 1;"
            , "    if (needed > packet_size) { return; }"
            , "    const uint32_t used = a + b;"
            , "    use(packet, used);"
            , "}"
            ] `shouldBeShort` []

        it "knows a variable made from one that is a sum" $
            [ "void use(const uint8_t *data, uint32_t length);"
            , "void f(uint8_t *packet, uint16_t packet_size, uint16_t a, uint16_t b) {"
            , "    const uint32_t needed = a + b + 9;"
            , "    if (needed > packet_size) { return; }"
            , "    const uint32_t plain_len = a + b;"
            , "    const uint32_t enc_len = plain_len + 8;"
            , "    use(packet, enc_len);"
            , "}"
            ] `shouldBeShort` []

        it "forgets what a variable is the sum of when one of them changes" $
            [ "void use(const uint8_t *data, uint32_t length);"
            , "void f(uint8_t *packet, uint16_t packet_size, uint16_t a, uint16_t b) {"
            , "    if (b + 1 > packet_size) { return; }"
            , "    const uint32_t used = a + b;"
            , "    a = b % 2;"
            , "    use(packet, used);"
            , "}"
            ] `shouldBeShort` ["use#1 vs #2: has 1, up to 131069"]

        it "counts a length in elements of what the buffers hold" $
            [ "GNU_ALLOC_SIZE(2, 3) void *mem_valloc(const Memory *mem, uint32_t nmemb, uint32_t size);"
            , "typedef struct Item { uint32_t a; uint8_t *b; } Item;"
            , "void f(const Memory *mem, const Item items[4], uint32_t n) {"
            , "    if (n > 4) { return; }"
            , "    Item *copy = (Item *)mem_valloc(mem, n, sizeof(Item));"
            , "    if (copy == nullptr) { return; }"
            , "    memcpy(copy, items, n * sizeof(Item));"
            , "    memcpy(copy, items, sizeof(Item) * (n + 1));"
            , "}"
            ] `shouldBeShort` ["memcpy#1 vs #3: has 0, up to 5", "memcpy#2 vs #3: has 4, up to 5"]

        it "takes the size of a local array from the sizes of other locals" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "void f(void) {"
            , "    uint8_t plain[40];"
            , "    uint8_t request[1 + sizeof(plain)];"
            , "    use(request, sizeof(request));"
            , "}"
            ] `shouldBeShort` []

    describe "what functions need of the buffers they're given" $ do
        it "infers what a function needs of a buffer it's given" $
            [ "static void put_key(uint8_t *out, const uint8_t key[32]) { memcpy(out, key, 32); }"
            , "void f(void) {"
            , "    uint8_t big[32];"
            , "    uint8_t small[16];"
            , "    uint8_t k[32] = {0};"
            , "    put_key(big, k);"
            , "    put_key(small, k);"
            , "}"
            ] `shouldBeShort` ["put_key#1 needs: has 16, up to 32"]

        it "infers a need that depends on another parameter" $
            [ "void seal(uint8_t *out, const uint8_t *data, uint16_t length) { memcpy(out, data, length); memset(out + length, 0, 16); }"
            , "void g(const uint8_t *data, uint16_t length) {"
            , "    uint8_t buf[64];"
            , "    if (length > 48) { return; }"
            , "    seal(buf, data, length);"
            , "}"
            , "void h(const uint8_t *data, uint16_t length) {"
            , "    uint8_t buf[64];"
            , "    if (length > 49) { return; }"
            , "    seal(buf, data, length);"
            , "}"
            ] `shouldBeShort` ["seal#1 needs: has 64, up to 65"]

        it "passes a need on to the function's own callers" $
            [ "static void put_key(uint8_t *out, const uint8_t key[32]) { memcpy(out, key, 32); }"
            , "static void wrap(uint8_t *packet, const uint8_t key[32]) { packet[0] = 1; put_key(packet + 1, key); }"
            , "void f(void) { uint8_t p[32]; uint8_t k[32] = {0}; wrap(p, k); }"
            ] `shouldBeShort` ["wrap#1 needs: has 32, up to 33"]

        it "doesn't infer what a function used as a value needs" $
            [ "typedef void put_cb(uint8_t *out);"
            , "void set_handler(put_cb *handler);"
            , "static void put(uint8_t *out) { memset(out, 0, 32); }"
            , "void f(uint8_t buf[16]) { set_handler(put); put(buf); }"
            ] `shouldBeShort` ["memset#1 vs #3: has 1, up to 32"]

        it "doesn't pass on a need for a length only its type bounds" $
            [ "void clear(uint8_t *data, size_t data_size);"
            , "static void seal(const uint8_t *plain, size_t length, uint8_t *out) {"
            , "    memcpy(out, plain, length);"
            , "    clear(out + length, PADDING);"
            , "}"
            , "void f(void) { uint8_t p[16] = {0}; uint8_t buf[64]; seal(p, 16, buf); }"
            ] `shouldBeShort` ["clear#1 vs #2: has 0, up to 18446744073709551615"]

        it "doesn't pass on a need for an argument only its type bounds" $
            [ "uint16_t read_length(void);"
            , "static void put(uint8_t *out, uint16_t count) { memset(out, 0, count); }"
            , "static void get(uint8_t *out) { put(out, read_length()); }"
            , "void f(void) { uint8_t buf[16]; get(buf); }"
            ] `shouldBeShort` ["put#1 needs: has 1, up to 65535"]

    describe "every way a value can change" $ do
        it "checks a call in a case that returns it" $
            [ "int use(const uint8_t key[32]);"
            , "int f(int kind) {"
            , "    uint8_t small[16];"
            , "    switch (kind) {"
            , "        case 1: return use(small);"
            , "    }"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 16"]

        it "sees what a function returns in a case" $
            [ "void use(const uint8_t key[32]);"
            , "static uint32_t key_size(int kind) {"
            , "    switch (kind) {"
            , "        case 1: return 16;"
            , "    }"
            , "    return 32;"
            , "}"
            , "int f(const uint8_t *data, uint32_t length, int kind) {"
            , "    if (length != key_size(kind)) { return -1; }"
            , "    use(data);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 16"]

        it "takes every definition of a function into account" $
            [ "void use(const uint8_t key[32]);"
            , "#ifdef SMALL_KEYS"
            , "static uint32_t key_size(void) { return 16; }"
            , "#else"
            , "static uint32_t key_size(void) { return 32; }"
            , "#endif /* SMALL_KEYS */"
            , "int f(const uint8_t *data, uint32_t length) {"
            , "    if (length != key_size()) { return -1; }"
            , "    use(data);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 16"]

        it "doesn't trust a guard on a subtraction that can wrap" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint32_t length, uint32_t offset) {"
            , "    if (length - offset < 32) { return -1; }"
            , "    use(data + offset);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past data + offset: has 0, 0..4294967295"]

        it "trusts a guard on a subtraction that can't wrap" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint32_t length, uint32_t offset) {"
            , "    if (offset > length) { return -1; }"
            , "    if (length - offset < 32) { return -1; }"
            , "    use(data + offset);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "follows a difference done in size_t back into an int" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length) {"
            , "    const int plain_len = (int)length - 16;"
            , "    const int body_len = plain_len - (sizeof(uint32_t) + 1);"
            , "    if (body_len < 32) { return -1; }"
            , "    use(data + 16 + sizeof(uint32_t) + 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "doesn't trust a difference that wraps in 32 bits as a 64 bit number" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint32_t length, uint32_t used) {"
            , "    const uint64_t rest = length - used;"
            , "    if (rest < 32) { return -1; }"
            , "    use(data + used);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past data + used: has 0, 0..4294967295"]

        it "doesn't trust a comparison that makes a negative number unsigned" $
            [ "void use(const uint8_t key[32]);"
            , "void f(uint32_t length, int32_t limit) {"
            , "    uint8_t buf[64];"
            , "    if (limit > 32) { return; }"
            , "    if (length > limit) { return; }"
            , "    use(buf + length);"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "past buf + length: has 64, 0..4294967295"]

        it "takes an argument as the parameter's type holds it" $
            [ "void use(const uint8_t key[32]);"
            , "static int helper(const uint8_t *data, uint16_t length) { use(data + 1); return 0; }"
            , "int f(const uint8_t *data) {"
            , "    const uint32_t big = 65546;"
            , "    return helper(data, big);"
            , "}"
            ] `shouldBeShort` ["helper#2 at least 33, is 0", "helper#1 vs #2: has 1, up to 65535"]

        it "takes a return value as the return type holds it" $
            [ "void use(const uint8_t key[32]);"
            , "static uint16_t key_size(void) { return 65536 + 16; }"
            , "int f(const uint8_t *data, uint32_t length) {"
            , "    if (length != key_size()) { return -1; }"
            , "    use(data);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0"]

        it "forgets a variable written through a pointer to it" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t *data, uint16_t length) {"
            , "    uint16_t checked = 0;"
            , "    uint16_t *alias = &checked;"
            , "    checked = 40;"
            , "    *alias = 0;"
            , "    if (length < checked) { return; }"
            , "    use(data);"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0"]

        it "joins an if without an else with what comes after it" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "void f(const uint8_t *src, uint16_t length) {"
            , "    if (length <= 16) { use(src, 0); }"
            , "    use(src, 20);"
            , "}"
            ] `shouldBeShort` ["use#1 vs #2: has 0, up to 20"]

        it "keeps a variable a function writes through a pointer it doesn't keep" $
            [ "void use(const uint8_t key[32]);"
            , "void other(void);"
            , "static void read_size(uint16_t *size) { *size = 40; }"
            , "void f(const uint8_t *data, uint16_t length) {"
            , "    uint16_t size;"
            , "    read_size(&size);"
            , "    if (size < 40) { return; }"
            , "    other();"
            , "    if (length < size) { return; }"
            , "    use(data);"
            , "}"
            ] `shouldBeShort` []

        it "forgets a variable a function may keep a pointer to" $
            [ "void use(const uint8_t key[32]);"
            , "void other(void);"
            , "void read_unseen(uint16_t *size);"
            , "static uint16_t *g_kept = nullptr;"
            , "static void keep(uint16_t *size) { g_kept = size; }"
            , "static void pass_on(uint16_t *size) { keep(size + 0); }"
            , "void f(const uint8_t *data, uint16_t length) {"
            , "    uint16_t a;"
            , "    uint16_t b;"
            , "    uint16_t c;"
            , "    read_unseen(&a);"
            , "    pass_on(&b);"
            , "    uint16_t *alias = &c;"
            , "    a = 40;"
            , "    b = 40;"
            , "    c = 40;"
            , "    other();"
            , "    if (length < a) { return; }"
            , "    use(data);"
            , "    if (length < b) { return; }"
            , "    use(data);"
            , "    if (length < c) { return; }"
            , "    use(data);"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0", "use#1 needs 32, has 0", "use#1 needs 32, has 0"]

        it "doesn't take the address of what a pointer points to as the pointer's" $
            [ "void use(const uint8_t key[32]);"
            , "void other(void);"
            , "void lookup(const uint8_t *public_key);"
            , "int f(const uint8_t *packet, uint16_t length) {"
            , "    if (length < 40) { return -1; }"
            , "    const uint8_t *public_key = &packet[1];"
            , "    lookup(public_key);"
            , "    other();"
            , "    use(packet + 1);"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "forgets a global variable a call can change" $
            [ "void use(const uint8_t key[32]);"
            , "static uint16_t g_size = 0;"
            , "void change(void);"
            , "void f(const uint8_t *data, uint16_t length) {"
            , "    g_size = 40;"
            , "    change();"
            , "    if (length < g_size) { return; }"
            , "    use(data);"
            , "}"
            ] `shouldBeShort` ["use#1 needs 32, has 0"]

        it "doesn't know a pointer field's size when it's set through its address" $
            [ "typedef struct Announce { const uint8_t *public_key; } Announce;"
            , "void use(const uint8_t key[32]);"
            , "void set_key(const uint8_t **slot, const uint8_t *pk);"
            , "void init(Announce *a, const uint8_t pk[32]) { a->public_key = pk; }"
            , "void init2(Announce *a, const uint8_t *pk) { set_key(&a->public_key, pk); }"
            , "void f(const Announce *a) { use(a->public_key); }"
            ] `shouldBeShort` ["use#1 needs 32, unknown"]

        it "takes a pointer field's size from what an initialiser gives it" $
            [ "typedef struct Announce { const uint8_t *public_key; } Announce;"
            , "void use(const uint8_t key[32]);"
            , "void announce(const Announce *a);"
            , "void init(Announce *a, const uint8_t pk[32]) { a->public_key = pk; }"
            , "void init2(const uint8_t *pk) { const Announce a = {pk}; announce(&a); }"
            , "void f(const Announce *a) { use(a->public_key); }"
            ] `shouldBeShort` ["use#1 needs 32, has 1"]

        it "knows a pointer field's size where an initialiser sets it to nullptr" $
            [ "typedef struct Announce { const uint8_t *public_key; } Announce;"
            , "typedef struct Peer { Announce announce; int x; } Peer;"
            , "void use(const uint8_t key[32]);"
            , "void announce(const Announce *a);"
            , "void init(Announce *a, const uint8_t pk[32]) { a->public_key = pk; }"
            , "void reset(Peer *p) { *p = (Peer) {0}; }"
            , "void none(void) { const Announce a = {nullptr}; announce(&a); }"
            , "void f(const Announce *a) { if (a->public_key != nullptr) { use(a->public_key); } }"
            ] `shouldBeShort` []

    describe "what's known through a variable given something else" $ do
        it "keeps what was known of a variable through one equal to it" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "int read_length(void);"
            , "void f(uint8_t *buf, uint16_t buf_size) {"
            , "    int expected = read_length();"
            , "    if (expected < 0 || expected > buf_size) { return; }"
            , "    const int got = read_length();"
            , "    if (got != expected) { return; }"
            , "    expected = 0;"
            , "    use(buf, got);"
            , "}"
            ] `shouldBeShort` []

        it "keeps what's known after a loop given a variable of the same name as an earlier one" $
            [ "void f(bool again) {"
            , "    unsigned int index = 4;"
            , "    for (unsigned int i = 0; i < 4; ++i) { if (again) { index = i; break; } }"
            , "    if (index == 4) { for (unsigned int i = 0; i < 2; ++i) { if (again) { index = i; } } assert(index <= 4); }"
            , "}"
            ] `shouldBeShort` []

        it "keeps a variable made from another no bigger than it where a branch made it smaller" $
            [ "void f(uint32_t n) { uint32_t i = n; if (i > 0) { --i; } assert(i <= n); }"
            ] `shouldBeShort` []

        it "keeps a copy of a field no bigger than it where a loop left by a break made it smaller" $
            [ "typedef struct List { uint32_t count; } List;"
            , "void f(const List *l) {"
            , "    uint32_t i = l->count;"
            , "    while (i > 0) { if (i == 7) { break; } --i; }"
            , "    assert(i <= l->count);"
            , "}"
            ] `shouldBeShort` []

    describe "loops" $ do
        it "knows how many elements an array given its elements has, and sizeof over its element's" $
            [ "typedef struct Pair { int a; int b; } Pair;"
            , "int f(Pair *p) {"
            , "  int *const fields[] = { &p->a, &p->b };"
            , "  int *last = nullptr;"
            , "  for (uint32_t j = 0; j < sizeof(fields) / sizeof(fields[0]); ++j) { last = fields[j]; }"
            , "  return last == nullptr;"
            , "}"
            ] `shouldBeShort` []

        it "knows a count-down loop's index stays within what its type holds" $
            [ "typedef struct Client { int x; } Client;"
            , "static int last(const Client *list, size_t length) {"
            , "  int s = 0;"
            , "  for (size_t i = length; i != 0; --i) { s = list[i - 1].x; }"
            , "  return s;"
            , "}"
            , "int f(void) { Client list[8] = {{0}}; return last(list, 8); }"
            ] `shouldBeShort` []

        it "keeps what a loop doesn't change as it was before the loop" $
            [ "int f(const uint8_t list[8], uint8_t n) {"
            , "  uint32_t i = 0;"
            , "  while (i < 8 && list[i] != n) { ++i; }"
            , "  if (i == 8) { return -1; }"
            , "  uint32_t j = 0;"
            , "  while (j < 8) { ++j; }"
            , "  return list[i];"
            , "}"
            ] `shouldBeShort` []

        it "narrows a for loop's body by its condition" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t keys[128]) { for (int i = 0; i < 4; ++i) { use(keys + i * 32); } }"
            ] `shouldBeShort` []

        it "narrows a do while loop's body by its condition when it goes round again" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t keys[128]) { int i = 0; do { use(keys + i * 32); ++i; } while (i < 4); }"
            ] `shouldBeShort` []

        it "keeps what a loop's condition says past branches in its body" $
            [ "void use(const uint8_t key[32]);"
            , "bool ready(int k);"
            , "void f(const uint8_t keys[128]) {"
            , "    for (int i = 0; i < 4; ++i) {"
            , "        if (ready(i)) { if (ready(0)) { ready(1); } }"
            , "        use(keys + i * 32);"
            , "    }"
            , "}"
            ] `shouldBeShort` []

        it "puts a loop's bound and a length check together" $
            [ "void use(const uint8_t key[32]);"
            , "int f(const uint8_t *data, uint16_t length, uint16_t count) {"
            , "    if (length < count * 32) { return -1; }"
            , "    for (uint16_t i = 0; i < count; ++i) { use(&data[i * 32]); }"
            , "    return 0;"
            , "}"
            ] `shouldBeShort` []

        it "keeps a count made in a loop no bigger than the loop's index" $
            [ "void use(const uint8_t key[32]);"
            , "bool good(int k);"
            , "int f(void) {"
            , "    int found[8];"
            , "    int count = 0;"
            , "    for (int i = 0; i < 8; ++i) {"
            , "        if (good(i)) { found[count] = i; ++count; }"
            , "    }"
            , "    return count;"
            , "}"
            ] `shouldBeShort` []

        it "keeps a cursor moved by the same step as a loop's index" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t data[256]) {"
            , "    uint16_t offset = 0;"
            , "    for (uint16_t j = 0; j < 8; ++j) { use(data + offset); offset += 32; }"
            , "}"
            ] `shouldBeShort` []

        it "reaches a for loop's step only through its body" $
            [ "int f(int n) { int j = 0; for (int i = 0; i < n; i = j + 1) { j = i; } return j; }"
            ] `shouldBeShort` []

        it "keeps an outer loop's bound on its index past an inner loop" $
            [ "bool same(uint32_t a, uint32_t b);"
            , "void f(void) {"
            , "    int32_t found[16];"
            , "    for (uint32_t i = 0; i < 16; ++i) {"
            , "        for (uint32_t j = 0; j < 4; ++j) { if (same(i, j)) { break; } }"
            , "        found[i] = 1;"
            , "    }"
            , "}"
            ] `shouldBeShort` []

        it "doesn't take a for loop left by a break as its condition being false" $
            [ "void use(const uint8_t *data, uint32_t length);"
            , "bool stop(uint32_t i);"
            , "void f(void) { uint32_t i; for (i = 10; i > 0; --i) { if (stop(i)) { break; } } uint8_t buf[4]; use(buf, i); }"
            ] `shouldBeShort` ["use#1 vs #2: has 4, up to 10"]

        it "doesn't take a while loop left by a break as its condition being false" $
            [ "void use(const uint8_t *data, uint32_t length);"
            , "bool stop(uint32_t i);"
            , "void f(void) { uint32_t i = 10; while (i > 0) { if (stop(i)) { break; } --i; } uint8_t buf[4]; use(buf, i); }"
            ] `shouldBeShort` ["use#1 vs #2: has 4, up to 10"]

        it "doesn't take a do while loop left by a break as its condition being false" $
            [ "void use(const uint8_t *data, uint32_t length);"
            , "bool stop(uint32_t i);"
            , "void f(void) { uint32_t i = 10; do { if (stop(i)) { break; } i = 0; } while (i > 0); uint8_t buf[4]; use(buf, i); }"
            ] `shouldBeShort` ["use#1 vs #2: has 4, up to 10"]

    describe "signed arithmetic that may overflow" $ do
        it "reports a signed product that may overflow" $
            [ "int area(uint16_t w, uint16_t h) { return w * h; }"
            ] `shouldBeShort` ["overflow 0..4294836225"]

        it "accepts signed arithmetic a condition bounds" $
            [ "int less(int x) { if (x < 100) { return x + 1; } return 0; }"
            , "int down(int x) { return x > 0 ? x - 1 : 0; }"
            , "bool small(int x) { return x < 100 && x + 1 < 50; }"
            , "int count(int n) { int k = 0; for (int i = 0; i < n; ++i) { k = i + 1; } return k; }"
            ] `shouldBeShort` []

        it "bounds a product of numbers that may be less than 0" $
            [ "bool is_small(int kind);"
            , "int node_size(int kind) { if (is_small(kind)) { return 39; } return -1; }"
            , "int total(int kind) { return 8 * node_size(kind); }"
            ] `shouldBeShort` []

        it "assumes signed arithmetic doesn't overflow once it's reported" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "int create(uint8_t *packet, size_t length, int body) {"
            , "    if (body < 0 || length < 1 + (size_t)body) { return -1; }"
            , "    packet[0] = 1;"
            , "    return 1 + body;"
            , "}"
            , "void f(int body) {"
            , "    uint8_t packet[64];"
            , "    const int len = create(packet, sizeof(packet), body);"
            , "    if (len == -1) { return; }"
            , "    use(packet, len);"
            , "}"
            ] `shouldBeShort` ["overflow 1..2147483648"]

    describe "asserts" $ do
        it "reports an assert on integers it can't show" $
            [ "int f(int x) { assert(x < 10); return x; }"
            ] `shouldBeShort` ["assert x < 10"]

        it "accepts an assert it can show" $
            [ "void f(uint8_t x, int *p) { assert(x < 256); assert(p != nullptr); }"
            ] `shouldBeShort` []

        it "knows a buffer that's nullptr has a length of 0" $
            [ "bool set(const uint8_t *data, uint32_t length) { if (data == nullptr) { assert(length == 0); return true; } return false; }"
            , "bool unset(const uint8_t *data, uint32_t length) { if (!data) { assert(length == 0); } return true; }"
            ] `shouldBeShort` []

        it "doesn't take an allocation that failed to have a length of 0" $
            [ "GNU_ALLOC_SIZE(1) void *mem_balloc(uint32_t size);"
            , "typedef struct Entry { uint8_t *data; uint32_t length; } Entry;"
            , "bool store(Entry *entry, uint32_t length) {"
            , "    uint8_t *data = (uint8_t *)mem_balloc(length);"
            , "    if (data == nullptr) { entry->data = nullptr; entry->length = length; return false; }"
            , "    entry->data = data;"
            , "    entry->length = length;"
            , "    return true;"
            , "}"
            ] `shouldBeShort` ["entry->data vs entry->length: has 0, up to 4294967295"]

        it "relies on an assert after it" $
            [ "void use(const uint8_t key[32]);"
            , "void f(const uint8_t *data, uint16_t length) { assert(length >= 32); use(data); }"
            ] `shouldBeShort` ["assert length >= 32"]

        it "passes an assert on to the callers of a function called by name" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "static void put(const uint8_t *data, uint16_t length) { assert(length < 100); use(data, length); }"
            , "void f(const uint8_t *data, uint16_t length) { if (length >= 100) { return; } put(data, length); }"
            , "void g(const uint8_t *data, uint16_t length) { put(data, length); }"
            ] `shouldBeShort` ["put#2 at most 99, is 65535"]

    describe "what inference makes of the code" $ do
        it "sees a return inference grouped with what comes before it" $ do
            let code =
                    [ "typedef struct Entry { uint8_t *data; uint32_t length; } Entry;"
                    , "bool store(Entry *entry, uint8_t *entry_data, uint32_t length) {"
                    , "    if (entry_data == nullptr) { entry->data = nullptr; return false; }"
                    , "    entry->data = entry_data;"
                    , "    entry->length = length;"
                    , "    return true;"
                    , "}"
                    ]
            direct <- sizeErrors code
            lowered <- loweredSizeErrors code
            direct `shouldSatisfy` (not . null)
            lowered `shouldMatchList` direct

    describe "what isn't checked here" $ do
        it "leaves nullptr to the nullability check" $
            [ "void use(const uint8_t key[_Nullable 32]);"
            , "void use2(const uint8_t key[_Nonnull 32]);"
            , "void f(void) { use(nullptr); use2(nullptr); }"
            ] `shouldBeShort` []

    describe "what calls change" $ do
        it "keeps what's known of a field of a struct bytes may be written to across a copy into another's array" $
            [ "typedef struct Node { uint8_t key[32]; } Node;"
            , "typedef struct Table { uint16_t count; } Table;"
            , "const Table *as_table(const uint8_t *bytes) { return (const Table *)bytes; }"
            , "static void copy(Node *n, const uint8_t k[32]) { memcpy(n->key, k, 32); }"
            , "uint8_t f(const Table *t, Node *n, const uint8_t k[32]) {"
            , "    uint8_t buf[4] = {0};"
            , "    if (t->count >= 4) { return 0; }"
            , "    copy(n, k);"
            , "    return buf[t->count];"
            , "}"
            ] `shouldBeShort` []

        it "keeps what's known of a field across a call that only stores to another" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "typedef struct Conn { uint32_t n; int y; } Conn;"
            , "static void touch_y(Conn *c) { c->y = 1; }"
            , "void f(Conn *c) { uint8_t buf[8]; if (c->n > 8) { return; } touch_y(c); fill(buf, c->n); }"
            ] `shouldBeShort` []

        it "forgets it across a call that stores to it" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "typedef struct Conn { uint32_t n; int y; } Conn;"
            , "static void touch_n(Conn *c) { c->n = 100; }"
            , "void f(Conn *c) { uint8_t buf[8]; if (c->n > 8) { return; } touch_n(c); fill(buf, c->n); }"
            ] `shouldBeShort` ["fill#1 vs #2: has 8, up to 100"]

        it "forgets it across a call that stores to the same field of another" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "typedef struct Conn { uint32_t n; int y; } Conn;"
            , "static void touch_n(Conn *d) { d->n = 100; }"
            , "void f(Conn *c, Conn *d) { uint8_t buf[8]; if (c->n > 8) { return; } touch_n(d); fill(buf, c->n); }"
            ] `shouldBeShort` ["fill#1 vs #2: has 8, up to 100"]

        it "keeps what's known of a field across a call that sets fresh memory" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "typedef struct Conn { uint32_t n; } Conn;"
            , "static void *zeroed(uint32_t size) { void *p = malloc(size); if (p != nullptr) { memset(p, 0, size); } return p; }"
            , "void f(Conn *c) { uint8_t buf[8]; if (c->n > 8) { return; } void *q = zeroed(4); free(q); fill(buf, c->n); }"
            ] `shouldBeShort` ["memset#1 vs #3: unknown, up to 4"]

        it "forgets a field of a struct given as bytes across a call that writes bytes through a void pointer" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "typedef struct Conn { uint32_t n; } Conn;"
            , "static void wipe(void *any) { memset(any, 0xff, 1); }"
            , "void f(Conn *c, void *other) { uint8_t buf[8]; if (c->n > 8) { return; } uint8_t *raw = (uint8_t *)c; raw[0] = 1; wipe(other); fill(buf, c->n); }"
            ] `shouldBeShort` ["fill#1 vs #2: has 8, up to 4294967295"]

        it "forgets a number given as bytes across a call that writes bytes through a void pointer" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "static uint32_t g_n = 0;"
            , "static void keep(void) { uint8_t *raw = (uint8_t *)&g_n; raw[0] = 1; }"
            , "static void wipe(void *any) { memset(any, 0xff, 1); }"
            , "void f(void *other) { uint8_t buf[8]; if (g_n > 8) { return; } wipe(other); fill(buf, g_n); }"
            ] `shouldBeShort` ["fill#1 vs #2: has 8, up to 4294967295"]

        it "doesn't know a field of a struct kept as a void pointer that's set as bytes" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "typedef struct Item { uint16_t n; } Item;"
            , "typedef struct Holder { void *object; } Holder;"
            , "void set(Item *it, uint16_t v) { if (v > 16) { return; } it->n = v; }"
            , "void hold(Holder *h, Item *it) { h->object = it; }"
            , "void wipe(Holder *h) { memset(h->object, 0xff, 1); }"
            , "void f(const Item *it) { uint8_t buf[16]; use(buf, it->n); }"
            ] `shouldBeShort` ["use#1 vs #2: has 16, up to 65535"]

        it "knows a field of a struct kept as a void pointer that a function gives back" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "typedef struct Item { uint16_t n; } Item;"
            , "typedef struct Holder { void *object; } Holder;"
            , "void set(Item *it, uint16_t v) { if (v > 16) { return; } it->n = v; }"
            , "void hold(Holder *h, Item *it) { h->object = it; }"
            , "void *held(const Holder *h) { return h->object; }"
            , "void f(const Item *it) { uint8_t buf[16]; use(buf, it->n); }"
            ] `shouldBeShort` []

        it "doesn't know a field of a struct kept as a void pointer that's set as bytes where it's given back" $
            [ "void use(const uint8_t *data, uint16_t length);"
            , "typedef struct Item { uint16_t n; } Item;"
            , "typedef struct Holder { void *object; } Holder;"
            , "void set(Item *it, uint16_t v) { if (v > 16) { return; } it->n = v; }"
            , "void hold(Holder *h, Item *it) { h->object = it; }"
            , "void *held(const Holder *h) { return h->object; }"
            , "void wipe(const Holder *h) { memset(held(h), 0xff, 1); }"
            , "void f(const Item *it) { uint8_t buf[16]; use(buf, it->n); }"
            ] `shouldBeShort` ["use#1 vs #2: has 16, up to 65535"]

        it "keeps what's known of a field across a call that stores only through what it's given" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "typedef struct Conn { uint16_t n; } Conn;"
            , "static void read_into(uint16_t *_Nonnull out) { *out = 1000; }"
            , "void f(Conn *c) { uint8_t buf[8]; uint16_t got; if (c->n > 8) { return; } read_into(&got); fill(buf, c->n); }"
            ] `shouldBeShort` []

        it "keeps what a pointer points to across a store to a field whose address is never taken" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "typedef struct Port { uint16_t port; } Port;"
            , "static void set_port(Port *p) { p->port = 1000; }"
            , "void f(const uint16_t *n, Port *p) { uint8_t buf[8]; if (*n > 8) { return; } set_port(p); fill(buf, *n); }"
            ] `shouldBeShort` []

        it "forgets it where the field's address is taken" $
            [ "void fill(uint8_t *buf, uint32_t length);"
            , "typedef struct Port { uint16_t port; } Port;"
            , "static void set_port(Port *p) { p->port = 1000; }"
            , "uint16_t *port_of(Port *q) { return &q->port; }"
            , "void f(const uint16_t *n, Port *p) { uint8_t buf[8]; if (*n > 8) { return; } set_port(p); fill(buf, *n); }"
            ] `shouldBeShort` ["fill#1 vs #2: has 8, up to 65535"]

        it "keeps an array field's length across writing bytes, which change only what's in it" $
            [ "typedef struct Topic { uint16_t length; uint8_t topic[32]; } Topic;"
            , "static void put_byte(uint8_t *_Nonnull out) { *out = 1; }"
            , "void f(uint8_t *data, uint16_t length, const Topic *t) { if (length < t->length + 1) { return; } put_byte(data); memcpy(data + 1, t->topic, t->length); }"
            ] `shouldBeShort` []

    describe "indexes" $ do
        it "keeps what's checked of an element at a constant" $
            [ "void fill(uint8_t *data, uint32_t length);"
            , "uint8_t f(void) {"
            , "    uint8_t plain[16];"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4) { return 1; }"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            ] `shouldBeShort` []

        it "knows the size of an array as long as an element says" $
            [ "void fill(uint8_t *data, uint16_t length);"
            , "void f(const uint8_t *packet, uint16_t length) {"
            , "    if (length < 2) { return; }"
            , "    const uint8_t count = packet[1];"
            , "    VLA(uint8_t, data, 20 + count);"
            , "    fill(data + 1, 19);"
            , "}"
            ] `shouldBeShort` []

        it "says how many an element may ask a buffer to have" $
            [ "uint8_t first(const uint8_t *data, uint8_t count);"
            , "static uint8_t sum(const uint8_t *data, uint8_t count) {"
            , "    uint8_t total = 0;"
            , "    for (uint8_t i = 0; i < count; ++i) { total += data[i]; }"
            , "    return total;"
            , "}"
            , "uint8_t f(const uint8_t *packet, uint16_t length) {"
            , "    if (length < 2) { return 0; }"
            , "    const uint8_t buf[4] = {0};"
            , "    return sum(buf, packet[1]);"
            , "}"
            ] `shouldBeShort` ["sum#1 needs: has 4, up to 255"]

        it "keeps what's checked of an element across calls given only the rest of the array" $
            [ "typedef struct Node { uint8_t key[32]; } Node;"
            , "static void fill(uint8_t *data, uint32_t length) { memset(data, 3, length); }"
            , "static void unpack(Node *nodes, const uint8_t *data) { memcpy(nodes[0].key, data, 32); }"
            , "uint8_t f(Node out[4]) {"
            , "    uint8_t plain[64];"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4) { return 1; }"
            , "    unpack(out, plain + 1);"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            ] `shouldBeShort` []

        it "forgets what's checked of an element when a call given the array changes it" $
            [ "static void fill(uint8_t *data, uint32_t length) { memset(data, 3, length); }"
            , "uint8_t f(void) {"
            , "    uint8_t plain[64];"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4) { return 1; }"
            , "    fill(plain, sizeof(plain));"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            , "static uint8_t *kept = nullptr;"
            , "static void keep(uint8_t *data) { kept = data; }"
            , "static void touch(void) { kept[0] = 200; }"
            , "uint8_t g(void) {"
            , "    uint8_t plain[64];"
            , "    keep(plain);"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4) { return 1; }"
            , "    touch();"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            ] `shouldBeShort` ["index buf[i]: has 4, 0..254", "index buf[i]: has 4, 0..254", "index kept[0]: unknown, 0..0"]

        it "keeps what's checked of an element across a call that may do anything but isn't given the array" $
            [ "typedef void run_cb(uint8_t *data);"
            , "static void fill(uint8_t *data, uint32_t length) { memset(data, 3, length); }"
            , "uint8_t f(run_cb *run, uint8_t *other) {"
            , "    uint8_t plain[64];"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4) { return 1; }"
            , "    run(other);"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            , "uint8_t g(run_cb *run) {"
            , "    uint8_t plain[64];"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4) { return 1; }"
            , "    run(plain + 1);"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            ] `shouldBeShort` ["index buf[i]: has 4, 0..254"]

        it "keeps the size of a parameter written as an array across a store through another pointer" $
            [ "typedef struct Opts { uint8_t *owned; } Opts;"
            , "bool set(Opts *options, const uint8_t data[], size_t length) {"
            , "    if (data == nullptr) { return false; }"
            , "    options->owned = nullptr;"
            , "    uint8_t *copy = (uint8_t *)malloc(length);"
            , "    if (copy == nullptr) { return false; }"
            , "    memcpy(copy, data, length);"
            , "    options->owned = copy;"
            , "    return true;"
            , "}"
            ] `shouldBeShort` []

        it "keeps an array of its own given to libsodium out of what other calls may change" $
            [ "typedef struct Node { uint8_t key[32]; } Node;"
            , "static int decrypt(uint8_t *plain, const uint8_t *encrypted, size_t length) {"
            , "    if (crypto_box_open_easy_afternm(plain, encrypted, length, encrypted, encrypted) != 0) { return -1; }"
            , "    return 0;"
            , "}"
            , "static void unpack(Node *nodes, const uint8_t *data) { memcpy(nodes[0].key, data, 32); }"
            , "uint8_t f(const uint8_t encrypted[64], Node out[4]) {"
            , "    uint8_t plain[64];"
            , "    if (decrypt(plain, encrypted, 64) != 0) { return 1; }"
            , "    if (plain[0] > 4) { return 1; }"
            , "    unpack(out, encrypted);"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            ] `shouldBeShort` []

        it "forgets what's checked of an element when the array changes" $
            [ "void fill(uint8_t *data, uint32_t length);"
            , "uint8_t f(void) {"
            , "    uint8_t plain[16];"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4) { return 1; }"
            , "    fill(plain, sizeof(plain));"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            , "uint8_t g(uint8_t j) {"
            , "    uint8_t plain[16];"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4 || j >= 16) { return 1; }"
            , "    plain[j] = 200;"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            , "uint8_t h(void) {"
            , "    uint8_t plain[16];"
            , "    fill(plain, sizeof(plain));"
            , "    if (plain[0] > 4) { return 1; }"
            , "    uint8_t *p = plain;"
            , "    p[0] = 200;"
            , "    uint8_t buf[4] = {0};"
            , "    for (uint8_t i = 0; i < plain[0]; ++i) { buf[i] = 1; }"
            , "    return buf[0];"
            , "}"
            ] `shouldBeShort` ["index buf[i]: has 4, 0..254", "index buf[i]: has 4, 0..254", "index buf[i]: has 4, 0..254"]

        it "knows what's left of a division by a count a loop shows is at least 1 is in the array" $
            [ "typedef struct Node { uint8_t key[32]; } Node;"
            , "typedef struct Table { Node *loaded_nodes; uint32_t num_loaded_nodes; uint32_t loaded_nodes_index; } Table;"
            , "void boot(Table *t, const uint8_t key[32]);"
            , "void connect(Table *t) {"
            , "    for (uint32_t i = 0; i < t->num_loaded_nodes; ++i) {"
            , "        const uint32_t index = t->loaded_nodes_index % t->num_loaded_nodes;"
            , "        boot(t, t->loaded_nodes[index].key);"
            , "        ++t->loaded_nodes_index;"
            , "    }"
            , "}"
            ] `shouldBeShort` []

        it "reports each of two uses written the same where it is" $ do
            (direct, inferred) <- errorLines
                [ "typedef struct Node { uint8_t key[32]; } Node;"
                , "void note(const Node *node);"
                , "void f(uint32_t n, bool again) {"
                , "    Node nodes[4] = {{{0}}};"
                , "    for (uint32_t i = 0; i < n; ++i) {"
                , "        note(&nodes[i]);"
                , "        if (again) { note(&nodes[i]); }"
                , "    }"
                , "}"
                ]
            (direct, inferred) `shouldBe` ([6, 7], [6, 7])

        it "knows what a callback may change from the functions given as one, whatever names their integer types go by" $
            [ "typedef uint32_t Number;"
            , "typedef void join_cb(void *object, uint32_t n);"
            , "typedef struct Item { int x; } Item;"
            , "typedef struct List { Item *items; uint32_t num_items; join_cb *on_join; void *object; } List;"
            , "static void set_x(List *l, uint32_t i) { if (i < l->num_items) { l->items[i].x = 0; } }"
            , "static void handler(void *object, Number n) { if (object != nullptr) { set_x((List *)object, n); } }"
            , "void reg(List *l) { l->on_join = handler; }"
            , "int f(List *l, uint32_t i) {"
            , "  if (i >= l->num_items) { return 0; }"
            , "  if (l->on_join != nullptr) { l->on_join(l->object, i); }"
            , "  return l->items[i].x;"
            , "}"
            ] `shouldBeShort` []

        it "keeps how two variables relate when one of them they're both related to is given something else" $
            [ "void f(int out[8], int n, int m) {"
            , "  if (n < 0 || n > 8 || m < 0) { return; }"
            , "  int used = 8 - n;"
            , "  if (used > m) { used = m; }"
            , "  for (int i = 0; i < used; ++i) { out[n + i] = 0; }"
            , "}"
            ] `shouldBeShort` []

        it "knows what a function returns from how it relates to a loop's index" $
            [ "bool ok(int x);"
            , "static int count(int out[8]) {"
            , "  int num = 0;"
            , "  for (size_t i = 0; i < 8; ++i) { if (ok((int)i)) { out[num] = 1; ++num; } }"
            , "  return num;"
            , "}"
            , "static void use(const int *list, uint16_t length) { for (uint16_t i = 0; i < length; ++i) { if (list[i] == 0) { return; } } }"
            , "void g(void) { int out[8]; const int n = count(out); if (n < 4) { return; } use(out, n); }"
            ] `shouldBeShort` []

        it "knows a pointer indexed below a count needs that many elements, and checks the callers" $
            [ "typedef struct Client { int x; } Client;"
            , "static bool in_list(const Client *list, uint16_t length, int x) { for (uint16_t i = 0; i < length; ++i) { if (list[i].x == x) { return true; } } return false; }"
            , "bool f(int x) { Client clients[8] = {0}; return in_list(clients, 8, x); }"
            , "bool g(int x) { Client clients[8] = {0}; return in_list(clients, 9, x); }"
            ] `shouldBeShort` ["in_list#1 needs: has 8, up to 9"]

        it "accepts an index below a local array's size" $
            [ "int f(void) { uint8_t a[4] = {0}; return a[3]; }"
            ] `shouldBeShort` []

        it "reports one past it" $
            [ "int f(void) { uint8_t a[4] = {0}; return a[4]; }"
            ] `shouldBeShort` ["index a[4]: has 4, 4..4"]

        it "accepts where an element is, one past the last" $
            [ "const uint8_t *f(const uint8_t a[4]) { return &a[4]; }"
            ] `shouldBeShort` []

        it "accepts an index checked against a buffer's length" $
            [ "int f(const uint8_t *data, uint16_t length, uint16_t i) { if (i >= length) { return -1; } return data[i]; }"
            ] `shouldBeShort` []

        it "reports one that isn't checked" $
            [ "int f(const uint8_t *data, uint16_t length, uint16_t i) { return data[i]; }"
            ] `shouldBeShort` ["index data[i]: has 0, 0..65535"]

        it "says a buffer moved forward further than it may be long has none" $
            [ "int f(const uint8_t a[8], uint8_t i) { if (i > 20) { return 0; } const uint8_t *p = a + i; return p[0]; }"
            ] `shouldBeShort` ["past a + i: has 8, 0..20", "index p[0]: has 0, 0..0"]

        it "knows what a lookup loop found is below the length it looked up to" $
            [ "int f(const uint8_t *data, uint16_t length, uint8_t key) {"
            , "  int index = -1;"
            , "  for (uint16_t i = 0; i < length; ++i) { if (data[i] == key) { index = i; break; } }"
            , "  if (index == -1) { return 0; }"
            , "  return data[index];"
            , "}"
            ] `shouldBeShort` []

        it "keeps a cursor moved forward as a count goes down" $
            [ "int f(void) {"
            , "  uint8_t data[16] = {0};"
            , "  const uint8_t *p = data + 8;"
            , "  uint16_t n = 8;"
            , "  while (n > 0 && p[0] == 0) { ++p; --n; }"
            , "  return n > 0 ? p[0] : 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows what's left over from dividing by a count is below it" $
            [ "typedef struct Entry { int x; } Entry;"
            , "typedef struct Ring { Entry *entries; uint32_t entries_count; uint32_t last; } Ring;"
            , "int f(const Ring *r) { if (r->entries_count == 0) { return 0; } const uint32_t index = r->last % r->entries_count; return r->entries[index].x; }"
            ] `shouldBeShort` []

        it "knows a number at most another and not it is less" $
            [ "int f(const uint8_t *data, uint16_t length) {"
            , "  for (uint32_t i = 0; i <= length; ++i) { if (i == length || data[i] == 0) { return (int)i; } }"
            , "  return 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows what a lookup returned is below the count it was given where it isn't the number for none" $
            [ "static uint32_t index_of(const uint8_t *list, uint32_t size, uint8_t x) {"
            , "  for (uint32_t i = 0; i < size; ++i) { if (list[i] == x) { return i; } }"
            , "  return UINT32_MAX;"
            , "}"
            , "int f(const uint8_t *list, uint32_t size, uint8_t x) { const uint32_t i = index_of(list, size, x); if (i == UINT32_MAX) { return -1; } return list[i]; }"
            , "int g(const uint8_t *list, uint32_t size, uint8_t x) { const uint32_t i = index_of(list, size, x); return list[i]; }"
            , "int h(const uint8_t *list, uint32_t size, uint8_t x) { uint32_t i = index_of(list, size, x); ++i; if (i == UINT32_MAX) { return -1; } return list[i]; }"
            ] `shouldBeShort` ["index list[i]: has 0, 0..4294967295", "index list[i]: has 0, 0..4294967294"]

        it "knows the operating system gives back at most as many events as asked for" $
            [ "int f(int fd, int out[8]) {"
            , "  int events[8];"
            , "  const int n = epoll_wait(fd, (void *)events, 8, 0);"
            , "  for (int i = 0; i < n; ++i) { out[i] = events[i]; }"
            , "  return n;"
            , "}"
            ] `shouldBeShort` []

        it "knows a random number below a count is, through a callback, where the count isn't 0" $
            [ "typedef uint32_t uniform_cb(void *self, uint32_t upper_bound);"
            , "typedef struct Random_Funcs { uniform_cb *uniform; } Random_Funcs;"
            , "typedef struct Random { const Random_Funcs *funcs; void *user_data; } Random;"
            , "static uint32_t os_uniform(void *self, uint32_t upper_bound) { return randombytes_uniform(upper_bound); }"
            , "static const Random_Funcs os_funcs = { os_uniform };"
            , "uint32_t random_range(const Random *rng, uint32_t upper) { return rng->funcs->uniform(rng->user_data, upper); }"
            , "int f(const Random *rng, const uint8_t list[8]) { return list[random_range(rng, 8)]; }"
            , "int g(const Random *rng, const uint8_t *data, uint16_t length) { if (length == 0) { return 0; } const uint32_t i = random_range(rng, length); return data[i]; }"
            , "int h(const Random *rng, const uint8_t *data, uint16_t length) { const uint32_t i = random_range(rng, length); return data[i]; }"
            ] `shouldBeShort` ["index data[i]: has 0, 0..65534"]

        it "knows how many elements a call through a pointer gives back from the functions given as one" $
            [ "typedef const uint8_t *get_key_cb(const void *self);"
            , "typedef struct Key_Funcs { get_key_cb *get_key; } Key_Funcs;"
            , "typedef struct Keys { uint8_t key[32]; } Keys;"
            , "static const uint8_t *os_get_key(const void *self) { const Keys *keys = (const Keys *)self; return keys->key; }"
            , "static const Key_Funcs os_funcs = { os_get_key };"
            , "void f(const Key_Funcs *funcs, uint8_t key[32]) { memcpy(key, funcs->get_key(nullptr), 32); }"
            ] `shouldBeShort` []

        it "keeps a count no bigger than a cursor moved at least so far each time round says" $
            [ "int count_entries(const uint8_t *data, uint32_t length);"
            , "int count_entries(const uint8_t *data, uint32_t length) {"
            , "  const uint8_t *init = data;"
            , "  uint32_t n = 0;"
            , "  while (length - (uint32_t)(data - init) >= 8) {"
            , "    const uint8_t skip = data[0];"
            , "    data += 8;"
            , "    if (length - (uint32_t)(data - init) < skip) { return -1; }"
            , "    data += skip;"
            , "    ++n;"
            , "  }"
            , "  return (int)n;"
            , "}"
            ] `shouldBeShort` []

        it "knows a found index is below the count where it isn't the number for none" $
            [ "int f(const uint8_t list[8], uint8_t x) {"
            , "  uint32_t index = UINT32_MAX;"
            , "  for (uint32_t i = 0; i < 8; ++i) { if (list[i] == x && index == UINT32_MAX) { index = i; } }"
            , "  if (index == UINT32_MAX) { return -1; }"
            , "  return list[index];"
            , "}"
            , "int g(const uint8_t *data, uint16_t length, uint8_t x) {"
            , "  uint32_t index = UINT32_MAX;"
            , "  for (uint32_t i = 0; i < length; ++i) { if (data[i] == x) { index = i; break; } }"
            , "  if (index == UINT32_MAX) { return -1; }"
            , "  return data[index];"
            , "}"
            ] `shouldBeShort` []

        it "knows a found index is below a count field where it isn't the number for none" $
            [ "typedef struct Item { int x; } Item;"
            , "typedef struct List { Item *items; uint32_t num_items; } List;"
            , "int f(const List *l) {"
            , "  uint32_t index = UINT32_MAX;"
            , "  for (uint32_t i = 0; i < l->num_items; ++i) { if (l->items[i].x == 0) { index = i; break; } }"
            , "  if (index == UINT32_MAX) { return -1; }"
            , "  return l->items[index].x;"
            , "}"
            ] `shouldBeShort` []

        it "knows an index either found or made room for is in the array" $
            [ "typedef struct Memory Memory;"
            , "GNU_ALLOC_SIZE(3, 4) void *mem_vrealloc(const Memory *mem, void *ptr, uint32_t nmemb, uint32_t size);"
            , "void *mem_vrealloc(const Memory *mem, void *ptr, uint32_t nmemb, uint32_t size) { return realloc(ptr, nmemb * size); }"
            , "typedef struct Item { bool valid; } Item;"
            , "typedef struct List { const Memory *mem; Item *items; uint32_t num_items; uint32_t items_capacity; } List;"
            , "static int reserve(List *l, uint32_t num) {"
            , "  if (num <= l->items_capacity) { return 0; }"
            , "  Item *tmp = (Item *)mem_vrealloc(l->mem, l->items, num, sizeof(Item));"
            , "  if (tmp == nullptr) { return -1; }"
            , "  l->items = tmp;"
            , "  l->items_capacity = num;"
            , "  return 0;"
            , "}"
            , "int add(List *l) {"
            , "  uint32_t index = UINT32_MAX;"
            , "  for (uint32_t i = 0; i < l->num_items; ++i) { if (!l->items[i].valid) { index = i; break; } }"
            , "  if (index == UINT32_MAX) {"
            , "    if (l->num_items >= INT32_MAX) { return -1; }"
            , "    if (reserve(l, l->num_items + 1) == -1) { return -1; }"
            , "    index = l->num_items;"
            , "  }"
            , "  if (index == l->num_items) { ++l->num_items; }"
            , "  l->items[index].valid = true;"
            , "  return 0;"
            , "}"
            ] `shouldBeShort` []

        it "knows an index found by a second lookup into the same variable" $
            [ "typedef struct Client { int pk; int ip; } Client;"
            , "static uint32_t index_of_pk(const Client *array, uint32_t size, int pk) { for (uint32_t i = 0; i < size; ++i) { if (array[i].pk == pk) { return i; } } return UINT32_MAX; }"
            , "static uint32_t index_of_ip(const Client *array, uint32_t size, int ip) { for (uint32_t i = 0; i < size; ++i) { if (array[i].ip == ip) { return i; } } return UINT32_MAX; }"
            , "static bool in_list(Client *list, uint16_t length, int pk, int ip) {"
            , "  uint32_t index = index_of_pk(list, length, pk);"
            , "  if (index != UINT32_MAX) { list[index].ip = ip; return true; }"
            , "  index = index_of_ip(list, length, ip);"
            , "  if (index == UINT32_MAX) { return false; }"
            , "  list[index].pk = pk;"
            , "  return true;"
            , "}"
            , "bool f(int pk, int ip) { Client list[8] = {{0}}; return in_list(list, 8, pk, ip); }"
            , "bool g(int pk, int ip) { Client big[1024] = {{0}}; return in_list(big, 1024, pk, ip); }"
            ] `shouldBeShort` []

        it "knows a found index fits an int from how it relates to the count" $
            [ "typedef struct Client { uint8_t pk[32]; int ip; int t; } Client;"
            , "bool pk_equal(const uint8_t *a, const uint8_t *b);"
            , "static uint32_t index_of_pk(const Client *array, uint32_t size, const uint8_t pk[32]) { assert(size == 0 || array != nullptr); for (uint32_t i = 0; i < size; ++i) { if (pk_equal(array[i].pk, pk)) { return i; } } return UINT32_MAX; }"
            , "static uint32_t index_of_ip(const Client *array, uint32_t size, int ip) { assert(size == 0 || array != nullptr); for (uint32_t i = 0; i < size; ++i) { if (array[i].ip == ip) { return i; } } return UINT32_MAX; }"
            , "static void update(int index, Client *c, int ip) { c->ip = index; }"
            , "static bool in_list(Client *list, uint16_t length, const uint8_t pk[32], int ip) {"
            , "  uint32_t index = index_of_pk(list, length, pk);"
            , "  if (index != UINT32_MAX) { update(index, &list[index], ip); return true; }"
            , "  index = index_of_ip(list, length, ip);"
            , "  if (index == UINT32_MAX) { return false; }"
            , "  list[index].t = 1;"
            , "  return true;"
            , "}"
            , "bool f(const uint8_t pk[32], Client list[8], int ip) { return in_list(list, 8, pk, ip); }"
            , "bool g(const uint8_t pk[32], Client big[1024], int ip) { return in_list(big, 1024, pk, ip); }"
            ] `shouldBeShort` []

        it "keeps knowing a found index through a second search" $
            [ "int f(const uint8_t list[8], uint8_t x, const uint8_t other[8]) {"
            , "  uint32_t index = UINT32_MAX;"
            , "  for (uint32_t i = 0; i < 8; ++i) { if (list[i] == x && index == UINT32_MAX) { index = i; } }"
            , "  if (index == UINT32_MAX) { return -1; }"
            , "  uint32_t found = UINT32_MAX;"
            , "  for (uint32_t i = 0; i < 8; ++i) { if (other[i] == x) { found = i; break; } }"
            , "  if (found == UINT32_MAX) { return -1; }"
            , "  return list[index] + other[found];"
            , "}"
            ] `shouldBeShort` []

        it "knows a length chosen with a buffer is how long it is" $
            [ "void f(bool big) {"
            , "  uint8_t small_list[8] = {0};"
            , "  uint8_t big_list[12] = {0};"
            , "  uint8_t *list;"
            , "  unsigned int len;"
            , "  if (big) { list = big_list; len = 12; } else { list = small_list; len = 8; }"
            , "  for (unsigned int k = 0; k < len; ++k) { list[k] = 1; }"
            , "}"
            ] `shouldBeShort` []

        it "reports a pointer moved past one past the end" $
            [ "const uint8_t *f(const uint8_t a[8], uint8_t i) { if (i > 20) { return nullptr; } return a + i; }"
            , "const uint8_t *g(const uint8_t a[8], uint8_t i) { if (i > 8) { return nullptr; } return a + i; }"
            ] `shouldBeShort` ["past a + i: has 8, 0..20"]

        it "reports an index that may be negative" $
            [ "int f(const uint8_t a[4], int i) { if (i >= 4) { return 0; } return a[i]; }"
            ] `shouldBeShort` ["index a[i]: has 4, -2147483648..3"]

        it "accepts a loop below a length" $
            [ "int find_zero(const uint8_t *data, uint16_t length) { for (uint16_t i = 0; i < length; ++i) { if (data[i] == 0) { return i; } } return -1; }"
            ] `shouldBeShort` []

        it "accepts an array indexed below its count" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint32_t num_peers; } Group;"
            , "int f(const Group *g, uint32_t i) { if (i >= g->num_peers) { return -1; } return g->peers[i].x; }"
            ] `shouldBeShort` []

        it "accepts an array indexed by a number a check of its count returned true for" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint32_t num_peers; } Group;"
            , "bool peer_exists(const Group *g, int32_t n) { return n >= 0 && (uint32_t)n < g->num_peers && g->peers[n].x != 0; }"
            , "int f(const Group *g, int32_t n) { if (!peer_exists(g, n)) { return -1; } return g->peers[n].x; }"
            ] `shouldBeShort` []

        it "doesn't take what such a check knew of a pointer it changed to hold at the call" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint32_t num_peers; } Group;"
            , "extern Group other;"
            , "bool peer_exists(const Group *g, int32_t n) { g = &other; return n >= 0 && (uint32_t)n < g->num_peers; }"
            , "int f(const Group *g, int32_t n) { if (!peer_exists(g, n)) { return -1; } return g->peers[n].x; }"
            ] `shouldBeShort` ["index g->peers[n]: has 0, 0..2147483647"]

        it "accepts an array indexed in a static function by what every call checked against its count" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint32_t num_peers; } Group;"
            , "static int get_x(const Group *g, uint32_t i) { return g->peers[i].x; }"
            , "int f(const Group *g, uint32_t i) { if (i >= g->num_peers) { return -1; } return get_x(g, i); }"
            , "void use(int x);"
            , "void h(const Group *g) { for (uint32_t i = 0; i < g->num_peers; ++i) { use(get_x(g, i)); } }"
            ] `shouldBeShort` []

        it "knows a static function's parameters are the same where every call gives them the same" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint32_t num_peers; } Group;"
            , "static int get_last(const Group *g, uint32_t n) { if (n == 0) { return -1; } return g->peers[n - 1].x; }"
            , "int f(const Group *g) { return get_last(g, g->num_peers); }"
            ] `shouldBeShort` []

        it "reports it where one call didn't check" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint32_t num_peers; } Group;"
            , "static int get_x(const Group *g, uint32_t i) { return g->peers[i].x; }"
            , "int f(const Group *g, uint32_t i) { if (i >= g->num_peers) { return -1; } return get_x(g, i); }"
            , "int h(const Group *g) { return get_x(g, 5); }"
            ] `shouldBeShort` ["index g->peers[i]: has 0, 0..4294967294"]

        it "accepts an array indexed by what a lookup below its count returned" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint16_t num_peers; } Group;"
            , "static int index_of(const Group *g, int x) { for (uint16_t i = 0; i < g->num_peers; ++i) { if (g->peers[i].x == x) { return i; } } return -1; }"
            , "int f(const Group *g, int x) { const int i = index_of(g, x); if (i == -1) { return 0; } return g->peers[i].x; }"
            ] `shouldBeShort` []

        it "follows a count it doesn't name, of a struct it gives calls, for what they say of it" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint16_t num_peers; } Group;"
            , "static int index_of(const Group *g, int x) { for (uint16_t i = 0; i < g->num_peers; ++i) { if (g->peers[i].x == x) { return i; } } return -1; }"
            , "static int get_x(const Group *g, int i) { return g->peers[i].x; }"
            , "int f(const Group *g, int x) { const int i = index_of(g, x); if (i == -1) { return 0; } return get_x(g, i); }"
            ] `shouldBeShort` []

        it "doesn't take a count a lookup may change to bound what it returned" $
            [ "typedef struct Peer { int x; } Peer;"
            , "typedef struct Group { Peer *peers; uint16_t num_peers; } Group;"
            , "int index_of(Group *g, int x);"
            , "int found(Group *g, int x) { for (uint16_t i = 0; i < g->num_peers; ++i) { if (g->peers[i].x == x) { return i; } } return -1; }"
            , "int f(Group *g, int x) { if (g->num_peers > 2) { return 0; } const int i = found(g, x); if (i == -1) { return 0; } index_of(g, x); return g->peers[i].x; }"
            ] `shouldBeShort` ["index g->peers[i]: has 0, 0..1"]

        it "knows how many elements a call made a buffer have where it says it did" $
            [ "typedef struct Memory Memory;"
            , "GNU_ALLOC_SIZE(3, 4) void *mem_vrealloc(const Memory *mem, void *ptr, uint32_t nmemb, uint32_t size);"
            , "void *mem_vrealloc(const Memory *mem, void *ptr, uint32_t nmemb, uint32_t size) { return realloc(ptr, nmemb * size); }"
            , "void mem_delete(const Memory *mem, void *ptr) { free(ptr); }"
            , "typedef struct Item { int x; } Item;"
            , "typedef struct List { const Memory *mem; Item *items; uint32_t count; } List;"
            , "static bool resize(List *l, uint32_t n) {"
            , "  if (n == 0) { mem_delete(l->mem, l->items); l->items = nullptr; return true; }"
            , "  Item *tmp = (Item *)mem_vrealloc(l->mem, l->items, n, sizeof(Item));"
            , "  if (tmp == nullptr) { return false; }"
            , "  l->items = tmp;"
            , "  return true;"
            , "}"
            , "static int grow(List *l, uint32_t n) {"
            , "  Item *tmp = (Item *)mem_vrealloc(l->mem, l->items, n, sizeof(Item));"
            , "  if (tmp == nullptr) { return -1; }"
            , "  l->items = tmp;"
            , "  return 0;"
            , "}"
            , "int add(List *l, int x) {"
            , "  if (l->count >= 100) { return -1; }"
            , "  if (!resize(l, l->count + 1)) { return -1; }"
            , "  l->items[l->count].x = x;"
            , "  ++l->count;"
            , "  return 0;"
            , "}"
            , "int push(List *l, int x) {"
            , "  if (l->count >= 100) { return -1; }"
            , "  if (grow(l, l->count + 1) == -1) { return -1; }"
            , "  l->items[l->count].x = x;"
            , "  ++l->count;"
            , "  return 0;"
            , "}"
            ] `shouldBeShort` []

        it "keeps knowing more of a buffer than a call says it made it have" $
            [ "typedef struct Memory Memory;"
            , "GNU_ALLOC_SIZE(3, 4) void *mem_vrealloc(const Memory *mem, void *ptr, uint32_t nmemb, uint32_t size);"
            , "void *mem_vrealloc(const Memory *mem, void *ptr, uint32_t nmemb, uint32_t size) { return realloc(ptr, nmemb * size); }"
            , "typedef struct Item { int x; } Item;"
            , "typedef struct List { const Memory *mem; Item *items; uint32_t num_items; } List;"
            , "static bool ensure_one(List *l) {"
            , "  if (l->num_items >= 1) { return true; }"
            , "  Item *tmp = (Item *)mem_vrealloc(l->mem, l->items, 1, sizeof(Item));"
            , "  if (tmp == nullptr) { return false; }"
            , "  l->items = tmp;"
            , "  return true;"
            , "}"
            , "int f(List *l) {"
            , "  if (l->num_items < 4) { return 0; }"
            , "  if (!ensure_one(l)) { return 0; }"
            , "  return l->items[3].x;"
            , "}"
            ] `shouldBeShort` []

        it "doesn't check what sizeof is of, which isn't evaluated" $
            [ "size_t f(const uint8_t *p) { return sizeof(p[10]); }"
            ] `shouldBeShort` []

    describe "pointers looked up again" $ do
        let groups =
                [ "typedef struct Peer { int x; uint16_t peer_number; } Peer;"
                , "typedef struct Group { Peer *peers; uint16_t num_peers; } Group;"
                , "typedef struct Groups { Group *chats; uint16_t num_chats; } Groups;"
                , "static Group *get_group(const Groups *g_c, uint32_t n) { if (n >= g_c->num_chats) { return nullptr; } return &g_c->chats[n]; }"
                , "static int peer_index_of(const Group *g, uint16_t peer_number) { for (uint16_t i = 0; i < g->num_peers; ++i) { if (g->peers[i].peer_number == peer_number) { return i; } } return -1; }"
                , "static int get_x(const Groups *g_c, uint32_t n, int peer_index) { const Group *g = get_group(g_c, n); if (g == nullptr) { return -1; } return g->peers[peer_index].x; }"
                ]
        it "takes a pointer a lookup returns as the place it's the address of, in every function looking it up" $
            (groups ++
            [ "int f(const Groups *g_c, uint32_t n, uint16_t peer_number) {"
            , "    const Group *g = get_group(g_c, n);"
            , "    if (g == nullptr) { return -1; }"
            , "    const int peer_index = peer_index_of(g, peer_number);"
            , "    if (peer_index == -1) { return -1; }"
            , "    return get_x(g_c, n, peer_index);"
            , "}"
            ]) `shouldBeShort` []

        it "knows an index a call returns is below a count the call may have changed" $
            [ "typedef struct Peer { int x; uint16_t peer_number; } Peer;"
            , "typedef struct Group { Peer *peers; uint32_t num_peers; } Group;"
            , "typedef struct Groups { Group *chats; uint16_t num_chats; } Groups;"
            , "static Group *get_group_c(const Groups *g_c, uint32_t groupnumber) { if (groupnumber >= g_c->num_chats) { return nullptr; } return &g_c->chats[groupnumber]; }"
            , "static int get_peer_index(const Group *g, uint16_t peer_number) {"
            , "  for (uint32_t i = 0; i < g->num_peers; ++i) { if (g->peers[i].peer_number == peer_number) { return i; } }"
            , "  return -1;"
            , "}"
            , "static int note_active(Groups *g_c, uint32_t groupnumber, uint16_t peer_number) {"
            , "  Group *g = get_group_c(g_c, groupnumber);"
            , "  if (g == nullptr) { return -1; }"
            , "  const int index = get_peer_index(g, peer_number);"
            , "  if (index != -1) { return index; }"
            , "  if (g->num_peers >= INT32_MAX) { return -1; }"
            , "  const uint32_t added = g->num_peers;"
            , "  ++g->num_peers;"
            , "  return added;"
            , "}"
            , "static int get_x(const Groups *g_c, uint32_t groupnumber, int peer_index) {"
            , "  const Group *g = get_group_c(g_c, groupnumber);"
            , "  if (g == nullptr) { return 0; }"
            , "  assert(peer_index >= 0 && (uint32_t)peer_index < g->num_peers);"
            , "  return 0;"
            , "}"
            , "int handle(Groups *g_c, uint32_t groupnumber, uint16_t peer_number, bool known) {"
            , "  const Group *g = get_group_c(g_c, groupnumber);"
            , "  if (g == nullptr) { return 0; }"
            , "  const int index = known ? get_peer_index(g, peer_number) : note_active(g_c, groupnumber, peer_number);"
            , "  if (index == -1) { return 0; }"
            , "  return get_x(g_c, groupnumber, index);"
            , "}"
            ] `shouldBeShort` ["g->peers vs g->num_peers: has 0, up to 2147483647"]

        it "takes a pointer made the address of a place, and never changed, as that place" $
            [ "typedef struct Node { int x; } Node;"
            , "typedef struct Table { Node to_bootstrap[8]; unsigned int num_to_bootstrap; } Table;"
            , "void add(Table *t, int x) {"
            , "  unsigned int *const num = &t->num_to_bootstrap;"
            , "  if (*num < 8) {"
            , "    t->to_bootstrap[*num].x = x;"
            , "    ++*num;"
            , "  }"
            , "}"
            ] `shouldBeShort` []

        it "doesn't take one looked up at another number as the same" $
            (groups ++
            [ "int f(const Groups *g_c, uint32_t n, uint32_t other, uint16_t peer_number) {"
            , "    const Group *g = get_group(g_c, n);"
            , "    if (g == nullptr) { return -1; }"
            , "    const int peer_index = peer_index_of(g, peer_number);"
            , "    if (peer_index == -1) { return -1; }"
            , "    return get_x(g_c, other, peer_index);"
            , "}"
            ]) `shouldBeShort` ["index g->peers[peer_index]: has 0, 0..65534"]

    describe "what integer fields hold" $ do
        let list =
                [ "typedef struct List { uint32_t count; } List;"
                , "static int find(const List *l, uint32_t x) { for (uint32_t i = 0; i < l->count; ++i) { if (i == x) { return i; } } return -1; }"
                , "static void drop(List *l, int i) { --l->count; }"
                , "void remove_x(List *l, uint32_t x) { if (l->count == 0) { return; } const int i = find(l, x); if (i >= 0) { drop(l, i); } }"
                , "void add(List *l) { if (l->count >= INT32_MAX) { return; } ++l->count; }"
                ]
        it "keeps a count no more than its growth checks let it be, where what takes it down shows it doesn't wrap round" $
            list `shouldBeShort` []

        it "doesn't where something takes it down that may wrap round" $
            (list ++
            [ "void clear_one(List *l) { --l->count; }"
            ]) `shouldBeShort` ["signed i to int, most 4294967294"]

    describe "converting to unsigned" $ do
        it "reports a number that may be negative cast to an unsigned type" $
            [ "uint32_t f(int i) { return (uint32_t)i; }"
            ] `shouldBeShort` ["unsigned i to uint32_t, least -2147483648"]

        it "accepts one checked not to be" $
            [ "uint32_t f(int i) { if (i < 0) { return 0; } return (uint32_t)i; }"
            ] `shouldBeShort` []

        it "accepts one checked on the left of &&" $
            [ "bool f(int i, uint32_t n) { return i >= 0 && (uint32_t)i < n; }"
            ] `shouldBeShort` []

        it "reports a negative constant made unsigned" $
            [ "uint16_t f(void) { return (uint16_t) -1; }"
            ] `shouldBeShort` ["unsigned -1 to uint16_t, least -1"]

        it "accepts unsigned numbers and constants that aren't negative" $
            [ "uint32_t f(uint16_t n) { return (uint32_t)n + (uint32_t)5; }"
            ] `shouldBeShort` []

        it "reports one returned from a function with an unsigned result" $
            [ "uint16_t f(void) { return -1; }"
            ] `shouldBeShort` ["unsigned -1 to uint16_t, least -1"]

        it "reports one given for an unsigned parameter" $
            [ "void use(uint32_t n);"
            , "void f(int i) { use(i); }"
            ] `shouldBeShort` ["unsigned i to uint32_t, least -2147483648"]

        it "reports one assigned to an unsigned variable" $
            [ "uint32_t f(int i) { uint32_t n = i; n = i; return n; }"
            ] `shouldBeShort` ["unsigned i to uint32_t, least -2147483648", "unsigned i to uint32_t, least -2147483648"]

        it "accepts ones that can't be negative" $
            [ "void use(uint32_t n);"
            , "uint16_t f(int i) { if (i < 0) { return 0; } use(i); uint32_t n = i; return 1; }"
            ] `shouldBeShort` []

        it "reports a number that may be too big for the signed type it's made" $
            [ "int32_t f(uint32_t n) { return (int32_t)n; }"
            ] `shouldBeShort` ["signed n to int32_t, most 4294967295"]

        it "accepts one checked to be small enough" $
            [ "int f(uint32_t n) { if (n > 1000) { return -1; } return n; }"
            ] `shouldBeShort` []

        it "accepts unsigned numbers of fewer bits than the signed type" $
            [ "int f(uint16_t n) { return n; }"
            ] `shouldBeShort` []

        it "reports a loop index given for a signed parameter where the count may be too big" $
            [ "void use(int i);"
            , "void f(uint32_t count) { for (uint32_t i = 0; i < count; ++i) { use(i); } }"
            ] `shouldBeShort` ["signed i to int, most 4294967294"]

        it "knows what a function returning a check has made sure of" $
            [ "void use(uint32_t n);"
            , "static bool valid(int i, uint32_t n) { return i >= 0 && (uint32_t)i < n; }"
            , "void f(int i, uint32_t n) { if (!valid(i, n)) { return; } use(i); }"
            , "void g(int i, uint32_t n) { if (valid(i, n)) { return; } use(i); }"
            ] `shouldBeShort` ["unsigned i to uint32_t, least -2147483648"]

        it "knows what dividing or combining the bits of numbers that aren't negative can't be negative" $
            [ "uint8_t quotient(uint16_t index) { const uint8_t i = index / 8; return i; }"
            , "uint8_t either(uint8_t a, uint8_t b) { const uint8_t d = a ^ b; return d; }"
            , "uint16_t both(uint8_t hi, uint8_t lo) { return ((uint16_t)hi << 8) | lo; }"
            , "uint8_t common(uint8_t a, uint8_t b) { const uint8_t d = a & b; return d; }"
            ] `shouldBeShort` []

        it "still reports one that can be" $
            [ "uint32_t quotient(int index) { const uint32_t i = index / 8; return i; }"
            ] `shouldBeShort` ["unsigned index / 8 to uint32_t, least -268435456"]

        it "works out a quotient whose divisor's range is empty" $
            rangeArith C.BopDiv (Range (Just 0) (Just 10)) (Range (Just 2) (Just 0)) `shouldBe` unknownRange

