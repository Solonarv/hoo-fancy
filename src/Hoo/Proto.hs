module Hoo.Proto where

import Data.IORef
import Data.Kind
import GHC.TypeLits

import Data.Vinyl.ARec

data PObj super fields = MkPObj
  { pobjSuper  :: super
  , pobjFields :: ARec AField fields
  }

data Fld = Symbol :# Type

data AField :: Fld -> Type where
  AField :: KnownSymbol s => IORef t -> AField (s ':# t)