{-# LANGUAGE GADTs #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecordWildCards #-}

-- | This module defines a resource-safe linear IO monad. It provide facilities
-- to add in your own resources.
--
-- Functions in this module are meant to be qualified.

-- XXX: This would be better as a multiplicity-parametric relative monad, but
-- until we have multiplicity polymorphism, we use a linear monad.

module System.IO.Resource where

import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import Prelude.Linear hiding (IO)
import qualified System.IO.Linear as Linear

newtype ReleaseMap = ReleaseMap (IntMap (Linear.IO ()))

newtype IO a = IO {
  unIO
    :: ReleaseMap
    -> Linear.IO (a, Unrestricted ReleaseMap)
  }

-- * Creating new types of resources

-- | The type of resources. Each safe resource is implemented as an abstract
-- newtype wrapper around @Resource R@ where @R@ is the unsafe variant of the
-- resource.
data UnsafeResource a where
  UnsafeResource :: Int -> a -> UnsafeResource a
  -- Note that both components are unrestricted.

unsafeRelease :: UnsafeResource a -> IO ()
unsafeRelease (UnsafeResource key _) = IO (releaseWith key)
  where
    releaseWith key (ReleaseMap releaseMap) = do
        releaser
        Linear.return ((), Unrestricted (ReleaseMap nextMap))
      where
        Linear.Builder {..} = Linear.builder -- used in the do-notation
        releaser = releaseMap IntMap.! key
        nextMap = IntMap.delete key releaseMap

-- XXX: long lines
unsafeAquire
  :: Linear.IO (Unrestricted a)
  -> (a -> Linear.IO ())
  -> IO (UnsafeResource a)
unsafeAquire acquire release = IO $ \releaseMap -> do
    Unrestricted resource <- acquire
    makeRelease releaseMap resource
  where
    Linear.Builder {..} = Linear.builder -- used in the do-notation
    makeRelease (ReleaseMap releaseMap) resource =
        Linear.return (UnsafeResource releaseKey resource, Unrestricted (ReleaseMap nextMap))
      where
        releaseKey =
          case IntMap.null releaseMap of
            True -> 0
            False -> fst (IntMap.findMax releaseMap) + 1
        releaseAction =
          release resource
        nextMap =
          IntMap.insert releaseKey releaseAction releaseMap
