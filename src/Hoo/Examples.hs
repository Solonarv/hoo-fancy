{-# LANGUAGE OverloadedLabels #-}
module Hoo.Examples where

import Data.Vinyl.Core

import Hoo.Named
import Hoo.Operations
import Hoo.Class

-- | A simple example class. It has one field, @val@, which holds a
-- mutable value.
type MutBox a = Sig '["val" :# Mut NoDefault a] '[]
clsMutBox :: Class (MutBox a)
clsMutBox = Class (EmptyMut #val :& RNil)
                  (RNil)

-- | A computation which creates a @'clsMutBox' @Int@
-- and sets its one field to @0@. Used for testing.
testInt :: IO (Object (MutBox Int))
testInt = runM $ new clsMutBox $ rec1 (#val := 0)

-- | A mutable box around a monoid.
type MutMonoid a = Sig '[ "val" :# Mut HasDefault a]
                       '[ "mempty" :# Static '[] (Poly a)
                        , "mappend" :# Static '[Self Object, Self Object] (Self Object)
                        , "eat" :# Inst '[Self Object] ()
                        ]
clsMutMonoid :: Monoid a => Class (MutMonoid a)
clsMutMonoid = Class (  Default #val mempty
                     :& RNil)
                     ( #mempty := (\_ -> return mempty)
                     :& #mappend := (\_ x y -> do
                        xVal <- x #. #val
                        yVal <- y #. #val
                        new clsMutMonoid $ rec1 (#val := Just (xVal <> yVal)))
                     :& #eat := (\self other -> do
                        oVal <- other #. #val
                        sVal <- self #. #val
                        self # #val #= (sVal <> oVal) )
                     :& RNil)

-- | An immutable box around a monoid.
type ImmutMonoid a = Sig '[ "val" :# Immut a]
                         '[ "mempty" :# Static '[] (Self Object)
                          , "mappend" :# Static '[Self Object, Self Object] (Self Object)
                          , "eatr" :# Inst '[Self Object] (Self Object)
                          , "eatl" :# Inst '[Self Object] (Self Object)
                          , "of" :# Static '[Poly a] (Self Object)
                          , "unwrap" :# Inst '[] (Poly a)
                          ]
