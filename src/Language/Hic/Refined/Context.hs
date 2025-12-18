{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE StrictData                 #-}

module Language.Hic.Refined.Context
    ( MappingContext (..)
    , MappingRefinements (..)
    , emptyContext
    , emptyRefinements
    , pushMapping
    , getMapping
    , setRefinement
    , deleteRefinement
    , getRefinement
    , unsafeGetTag
    , unsafeGetId
    ) where

import           Data.Aeson         (ToJSON)
import           Data.Bits          (shiftL, shiftR, xor, (.&.), (.|.))
import           Data.Hashable      (Hashable (..))
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import           Data.Word          (Word16, Word32, Word64)
import           GHC.Generics       (Generic)

-- | The Variable Mapping Context (Γ) used for existential bisimulation.
-- Represented as a 128-bit bitfield.
--
-- Word 1: [ 0-7: Count | 8-63: Items 0-13 (4 bits each) ]
-- Word 2: [ 0-63: Items 14-29 (4 bits each) ]
data MappingContext = MappingContext {-# UNPACK #-} Word64 {-# UNPACK #-} Word64
    deriving (Show, Eq, Ord, Generic)

instance Hashable MappingContext where
    hashWithSalt s (MappingContext w1 w2) = s `hashWithSalt` w1 `hashWithSalt` w2

instance ToJSON MappingContext

-- | Persistent refinements for Skolem variables.
data MappingRefinements = MappingRefinements
    { mrRefinements :: IntMap Word32
    , mrHash        :: {-# UNPACK #-} Word64
    }
    deriving (Show, Generic)

instance ToJSON MappingRefinements

instance Eq MappingRefinements where
    (MappingRefinements _ h1) == (MappingRefinements _ h2) = h1 == h2

instance Ord MappingRefinements where
    compare (MappingRefinements _ h1) (MappingRefinements _ h2) = compare h1 h2

emptyContext :: MappingContext
emptyContext = MappingContext 0 0

emptyRefinements :: MappingRefinements
emptyRefinements = MappingRefinements IntMap.empty 0

-- | Pushes a new mapping onto the context (stack-like).
pushMapping :: Int -> MappingContext -> MappingContext
pushMapping mapping (MappingContext w1 w2) =
    let count :: Int
        count = fromIntegral (w1 .&. 0xFF)
        newCount = fromIntegral (min 30 (count + 1)) :: Word64

        -- Item at index 13 in w1 (bits 60-63) moves to index 14 in w2 (bits 0-3).
        item13 = (w1 `shiftR` 60) .&. 0xF

        -- w2 items shift left 4 bits. Bits 0-3 become item13.
        newW2 = (w2 `shiftL` 4) .|. item13

        -- w1 items 0-12 shift left 4 bits. Bits 8-11 become the new mapping.
        -- Bits 0-7 are the count.
        w1Data = (w1 `shiftR` 8) .&. 0x00FFFFFFFFFFFFFF
        shiftedW1 = (w1Data `shiftL` 4) .&. 0x00FFFFFFFFFFFFFF
        newW1 = (shiftedW1 `shiftL` 8) .|. ((fromIntegral mapping .&. 0xF) `shiftL` 8) .|. newCount
    in MappingContext newW1 newW2

-- | Retrieves a mapping by its De Bruijn index.
getMapping :: Int -> MappingContext -> Maybe Int
getMapping idx (MappingContext w1 w2) =
    let count = fromIntegral (w1 .&. 0xFF)
    in if idx >= count || idx >= 30 then Nothing
       else if idx < 14
            then Just $ fromIntegral ((w1 `shiftR` (8 + idx * 4)) .&. 0xF)
            else Just $ fromIntegral ((w2 `shiftR` ((idx - 14) * 4)) .&. 0xF)

-- | Records a refinement for a variable.
setRefinement :: Int -> Word32 -> MappingRefinements -> MappingRefinements
setRefinement key nodeID r =
    case IntMap.lookup key (mrRefinements r) of
        Just oldID | oldID == nodeID -> r
        Just oldID ->
            let newMap = IntMap.insert key nodeID (mrRefinements r)
                newHash = mrHash r `xor` fromIntegral (hash (key, oldID)) `xor` fromIntegral (hash (key, nodeID))
            in r { mrRefinements = newMap, mrHash = newHash }
        Nothing ->
            let newMap = IntMap.insert key nodeID (mrRefinements r)
                newHash = mrHash r `xor` fromIntegral (hash (key, nodeID))
            in r { mrRefinements = newMap, mrHash = newHash }

-- | Removes a refinement.
deleteRefinement :: Int -> MappingRefinements -> MappingRefinements
deleteRefinement key r =
    case IntMap.lookup key (mrRefinements r) of
        Nothing -> r
        Just oldID ->
            let newMap = IntMap.delete key (mrRefinements r)
                newHash = mrHash r `xor` fromIntegral (hash (key, oldID))
            in r { mrRefinements = newMap, mrHash = newHash }

-- | Retrieves a persistent refinement.
getRefinement :: Int -> MappingRefinements -> Maybe Word32
getRefinement key r = IntMap.lookup key (mrRefinements r)

-- | Dummy helper to satisfy existing API (to be removed after refactoring callers).
unsafeGetTag :: Int -> MappingRefinements -> Word16
unsafeGetTag _ _ = 0

-- | Internal helper to retrieve an ID without verification.
-- ONLY for use in tests.
unsafeGetId :: Int -> MappingRefinements -> Word32
unsafeGetId idx r = IntMap.findWithDefault 0 idx (mrRefinements r)
