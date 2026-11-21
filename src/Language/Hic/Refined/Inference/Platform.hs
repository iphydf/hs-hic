{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
-- | What hic is told of the operating systems' C interfaces that toxcore's
-- platform code uses: casts those interfaces need that types can't show to
-- be right. These are trusted, not checked, so there are as few as can be,
-- each one the interface's own rule. Toxcore's own types get none.
module Language.Hic.Refined.Inference.Platform
    ( sameObject
    , isHandle
    , isStringPointer
    , readOnlyStrings
    , checkPlatformUse
    , storesNothing
    , bytesWrittenThrough
    , keepsNothing
    , returnsZeros
    , writesOnlyZeros
    , returnsAtMost
    , returnsBelow
    ) where

import           Data.Fix                 (Fix (..))
import           Data.Foldable            (toList)
import           Data.List                (isPrefixOf, nubBy)
import           Data.Map.Strict          (Map)
import qualified Data.Map.Strict          as Map
import qualified Data.Set                 as Set
import           Data.Text                (Text)
import qualified Data.Text                as T
import           Language.Cimple          (Lexeme (..), NodeF (..))
import qualified Language.Cimple          as C
import           Language.Hic.Core.Errors (Context (..), ErrorInfo (..),
                                           TypeError (..))

-- | Whether a pointer to one of these types may be cast to the other: kinds
-- of socket address. A @sockaddr_storage@ has room and alignment for every
-- kind, and each kind starts with the family that says which it is (POSIX).
sameObject :: Text -> Text -> Bool
sameObject a b = Set.member a addresses && Set.member b addresses
  where
    addresses = Set.fromList ["sockaddr", "sockaddr_storage", "sockaddr_in", "sockaddr_in6"]

-- | A Windows @HANDLE@, which a socket's number is (@SOCKET@ is a
-- @UINT_PTR@): AFD polling takes the socket as one.
isHandle :: Text -> Bool
isHandle = (== "HANDLE")

-- | A Windows string that may be written to.
isStringPointer :: Text -> Bool
isStringPointer = (== "LPSTR")

-- | Windows functions that take a string as an 'isStringPointer' and only
-- read it, by the parameter (from 0): a @const@ string may be given there.
readOnlyStrings :: Map Text [Int]
readOnlyStrings = Map.fromList [("WSAStringToAddressA", [0])]

-- | Each use of the operating system's types and functions outside the
-- platform layer (the @os_@ files): the rest of toxcore stays clean of them.
checkPlatformUse :: [(FilePath, [C.Node (Lexeme Text)])] -> [ErrorInfo p]
checkPlatformUse files =
    [ ErrorInfo (Just l) [InFile path] (PlatformOutsideItsLayer what) []
    | (path, nodes) <- files
    , not ("os_" `isPrefixOf` reverse (takeWhile (/= '/') (reverse path)))
    , (l, what) <- nubBy sameLine (concatMap uses nodes)
    ]
  where
    sameLine (L (C.AlexPn _ a _) _ x, w) (L (C.AlexPn _ b _) _ y, v) = a == b && w == v && x == y
    uses (Fix node) = here node ++ concatMap uses (toList node)
    here = \case
        TyStruct l@(L _ _ t) | Set.member t structs   -> [(l, "struct " <> t)]
        TyStd l@(L _ _ t) | Set.member t names        -> [(l, t)]
        TyUserDefined l@(L _ _ t) | Set.member t names -> [(l, t)]
        FunctionCall (Fix (VarExpr l@(L _ _ f))) _ | Set.member f functions -> [(l, f)]
        _ -> []
    structs = Set.fromList
        [ "sockaddr", "sockaddr_storage", "sockaddr_in", "sockaddr_in6", "in_addr", "in6_addr"
        , "addrinfo", "ifreq", "ifconf", "ifaddrs", "epoll_event", "pollfd" ]
    names = Set.fromList
        [ "socklen_t", "sa_family_t", "in_addr_t", "in_port_t", "nfds_t"
        , "SOCKET", "HANDLE", "DWORD", "LPDWORD", "WORD", "BYTE", "INT", "LPINT", "u_long"
        , "LPSTR", "LPCSTR", "LPSOCKADDR", "IP_ADAPTER_INFO", "WSADATA" ]
    functions = Set.fromList
        [ "socket", "bind", "listen", "accept", "connect", "send", "sendto", "recv", "recvfrom"
        , "setsockopt", "getsockopt", "getaddrinfo", "freeaddrinfo", "inet_pton", "inet_ntop"
        , "ioctl", "ioctlsocket", "fcntl", "poll", "select", "getifaddrs", "freeifaddrs"
        , "epoll_create", "epoll_create1", "epoll_ctl", "epoll_wait"
        , "closesocket", "GetAdaptersInfo", "DeviceIoControl", "WSAStartup", "WSACleanup"
        , "WSAGetLastError", "WSAPoll", "WSAAddressToStringA", "WSAStringToAddressA" ]

-- | The C library's functions for memory, and libsodium's, which keep
-- none of the pointers they're given past the call.
keepsNothing :: Text -> Bool
keepsNothing f = f `elem` ["memcpy", "memmove", "memset", "memcmp"]
    || any (`T.isPrefixOf` f) ["crypto_", "randombytes_", "sodium_"]

-- | The C library's functions that give back memory all zeros.
returnsZeros :: Text -> Bool
returnsZeros = (== "calloc")

-- | The C library's functions that only allocate and free memory: they
-- store nothing the program has.
storesNothing :: Text -> Bool
storesNothing = (`Set.member` Set.fromList ["malloc", "calloc", "realloc", "free"])

-- | The parameters (by position) the C library's (and libsodium's)
-- functions for memory and strings write bytes through: what they're given
-- there may be anything after. Freeing writes nothing anything still has.
-- 'Nothing' for any other function.
bytesWrittenThrough :: Text -> Maybe [Int]
bytesWrittenThrough = (`Map.lookup` Map.fromList
    [ ("memcpy", [0]), ("memmove", [0]), ("memset", [0])
    , ("memcmp", []), ("strlen", []), ("strnlen", []), ("strcmp", []), ("strncmp", [])
    , ("malloc", []), ("calloc", []), ("realloc", []), ("free", [])
    , ("sodium_malloc", []), ("sodium_free", []) ])

-- | What the operating system's functions for waiting on sockets return
-- at most, unless they fail with a number less than 0: so much more than
-- an argument (by position), the most events or sockets they're asked for.
returnsAtMost :: Text -> Map Int Integer
returnsAtMost f = Map.findWithDefault Map.empty f $ Map.fromList
    [ ("epoll_wait", Map.singleton 2 0), ("poll", Map.singleton 1 0), ("WSAPoll", Map.singleton 1 0) ]

-- | The argument (by position) libsodium's functions for random numbers
-- return less than, where it's at least 1, else 0 (@randombytes_uniform@).
returnsBelow :: Text -> Maybe Int
returnsBelow = (`Map.lookup` Map.fromList [("randombytes_uniform", 0)])

-- | Whether a call to the C library (or libsodium) writes only zeros, as
-- structs start: @memset@ with 0, @sodium_memzero@.
writesOnlyZeros :: Text -> [C.Node (Lexeme Text)] -> Bool
writesOnlyZeros "sodium_memzero" _                                     = True
writesOnlyZeros "memset" (_ : Fix (LiteralExpr C.Int (L _ _ "0")) : _) = True
writesOnlyZeros _ _                                                    = False
