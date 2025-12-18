{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData    #-}

module Language.Hic.Refined.State
    ( ProductState (..)
    ) where

import           Data.Aeson                     (ToJSON)
import           Data.Text                      (Text)
import           Data.Word                      (Word32)
import           GHC.Generics                   (Generic)
import           Language.Cimple                (Lexeme)
import           Language.Hic.Refined.Context   (MappingContext (..),
                                                 MappingRefinements (..))
import           Language.Hic.Refined.LatticeOp (Polarity (..))
import           Language.Hic.Refined.Types     (TemplateId)

-- | The optimized state for the Product Automaton memoization table.
--
-- Field ordering is optimized for 'Ord': Node IDs are checked first as they
-- are the most likely to differ, followed by the polarity, context, and refinements.
--
-- Using primitive Word32 IDs and a bitfield-compressed context
-- enables register-level integer comparisons for O(1) state identification.
data ProductState = ProductState
    { psNodeL     :: Word32             -- ^ ID of the node in the left graph
    , psNodeR     :: Word32             -- ^ ID of the node in the right graph
    , psPolarity  :: Polarity           -- ^ Current operation (Join/Meet)
    , psOneWay    :: Bool               -- ^ True if this is a one-way inheritance (L inherits from R)
    , psGamma     :: {-# UNPACK #-} MappingContext     -- ^ Alpha-equivalent mapping context
    , psDepthL    :: {-# UNPACK #-} Int                -- ^ Absolute depth in left graph
    , psDepthR    :: {-# UNPACK #-} Int                -- ^ Absolute depth in right graph
    , psParentVar :: Maybe (Int, TemplateId)           -- ^ (Depth, Tid) of variable that triggered this sub-problem
    , psOrigin    :: Maybe (Lexeme Text)               -- ^ Source location of the constraint that triggered this state
    , psFile      :: Maybe FilePath                    -- ^ Source file of the constraint
    }
    deriving (Show, Eq, Ord, Generic)

instance ToJSON ProductState
