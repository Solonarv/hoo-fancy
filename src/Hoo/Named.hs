{-# LANGUAGE UndecidableInstances #-}
module Hoo.Named
  ( Named(..)
  , UnNamed, NameOf
  , type FindNamed
  , Label(..)
  ) where

import Data.Kind
import Data.Proxy
import GHC.TypeLits
import GHC.OverloadedLabels
  
-- | The type of named things (e.g. methods, fields).
data Named e = Symbol :# e

-- | Unwrap a @'Named'@
type family UnNamed n where
  UnNamed (s :# e) = e

type family NameOf n where
  NameOf (s :# e) = s

-- | Find a named thing in a list of named things.
-- >>> :kind! FindNamed "field" "foo" '["foo" :# Int, "bar" :: Bool]
-- Int :: Type
-- >>> :kind! FindNamed "field" "nope" '["foo" :# Int, "bar" :: Bool]

type family FindNamed (sort :: Symbol) (needle :: Symbol) (assocs :: [Named e]) :: Named e where
  FindNamed s n ((n :# e) : as) = (n :# e)
  FindNamed s n (a : as) = FindNamed s n as
  FindNamed s n '[] = TypeError ('Text (AppendSymbol (AppendSymbol "No " s) "named ") :<>: 'ShowType s)

-- | A specialised @'Proxy'@, for use with @OverloadedLabels@.
data Label (s :: Symbol) = Label

-- | Shows the symbol as well, i.e. @show (Label \@"foo")@ produces @Label \@"foo"@.
instance KnownSymbol s => Show (Label s) where
  showsPrec p _ = showParen (p > 10) $
    showString "Label @\"" . showString (symbolVal @s Proxy) . showString "\""

instance s ~ s' => IsLabel s (Label s') where
  fromLabel = Label