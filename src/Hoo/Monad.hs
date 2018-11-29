module Hoo.Monad where

-- | The monad in which Hoo operations run. This is really just
-- a wrapper over @IO@, but the constructor will be hidden,
-- so arbitrary IO is not possible.
newtype M a = M { runM :: IO a }
  deriving newtype (Functor, Applicative, Monad)