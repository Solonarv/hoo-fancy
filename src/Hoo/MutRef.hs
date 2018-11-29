module Hoo.MutRef where

import Data.IORef

import Hoo.Monad

-- | A mutable reference. Internally just an @'IORef'@.
newtype MutRef a = MutRef (IORef a)

-- | Create a new mutable reference.
newRef :: a -> M (MutRef a)
newRef = M . fmap MutRef . newIORef

-- | Read out a mutable reference's value
deref :: MutRef a -> M a
deref (MutRef ref) = M (readIORef ref)

-- | Set a mutable reference's value.
infix 2 #=
(#=) :: forall f s t i. MutRef t -> t -> M ()
(MutRef ref) #= x = M (writeIORef ref x)