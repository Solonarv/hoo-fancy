{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}
module Hoo.Class where

import Data.Kind
import GHC.TypeLits

import Data.Vinyl.ARec
import Data.Vinyl.Core
import Data.Vinyl.Functor
import Data.Vinyl.Lens
import Data.Vinyl.TypeLevel
import Data.Vinyl.XRec

import Hoo.Monad
import Hoo.MutRef
import Hoo.Named

-- * Signatures and classes

-- | The type of classes. A class declaration looks like this:
--
-- > type IntPair = Sig '["fst" :# Immut Int, "snd" :# Immut Int] '["sum" :# Inst '[] Int]
-- > clsIntPair :: Class IntPair
-- > clsIntPair = Class (  MustFill #fst
-- >                    :& MustFill #snd
-- >                    :& RNil)
-- >                    (#sum := (\self -> do
-- >                      return ( self #. #fst
-- >                             + self #. #snd))
-- >                    :& RNil)
--
-- This declares a class @IntPair@, with two immutable fields @fst :: Int@, @snd :: Int@
-- and one method, @sum :: self -> Int@, which returns the sum of @fst@ and @snd@.
data Class (sig :: Signature) = Class
  { clsFields :: Rec (FieldInitializer sig) (SigFields sig)
  , clsMethods :: Rec (MethodImpl sig) (SigMethods sig)
  }

-- | An object is a reference to the class, and a record of its fields.
data Object (sig :: Signature) = Object
  { objClass  :: Class sig
  , objFields :: ARec FieldVal (SigFields sig)
  }

-- | A class signature, i.e. a list of field and method descriptions.
data Signature = Sig [Named FieldDesc] [Named MethodDesc]

-- | Extract a signature's fields
type family SigFields sig where
  SigFields (Sig fs ms) = fs

-- | Extract a signature's methods
type family SigMethods sig where
  SigMethods (Sig fs ms) = ms

-- | Do the signature's fields contain @f@?
type HasField sig f = RElem f (SigFields sig) (RIndex f (SigFields sig))

-- ###########################################################
-- * Fields


-- | A field description, i.e. its type, mutability, and initializer type.
data FieldDesc = Immut Type
               | Mut HasDefaultVal Type
               | Alloc Type

-- | Whether a mutable field has a default value.
data HasDefaultVal = NoDefault | HasDefault

-- | Initializer for a field.
data FieldInitializer (sig :: Signature) (f :: Named FieldDesc) where
  -- | This field is immutable, it must be given a value.
  MustFill :: (KnownSymbol s, HasField sig (s :# Immut t))
           => !(Label s)
           -> FieldInitializer sig (s :# Immut t)
  -- | This field is mutable, and must be given a value.
  EmptyMut :: (KnownSymbol s, HasField sig (s :# Mut NoDefault t))
           => !(Label s)
           -> FieldInitializer sig (s :# Mut NoDefault t)
  -- | This field is mutable, but has a sensible default value.
  Default  :: (KnownSymbol s, HasField sig (s :# Mut HasDefault t))
           => !(Label s)
           -> t
           -> FieldInitializer sig (s :# Mut HasDefault t)
  -- | This field holds an allocated resource (RAII-style), this is the initializer.
  Allocate :: (KnownSymbol s, HasField sig (s :# Alloc t))
           => !(Label s)
           -> (Class sig -> M t)
           -> FieldInitializer sig (s :# Alloc t)

-- | Wrapper that holds a field value.
data FieldVal f where
  FVImmut  :: KnownSymbol s =>         !t  -> FieldVal (s :# (Immut t))
  FVMutRef :: KnownSymbol s => !(MutRef t) -> FieldVal (s :# (Mut i t))
  FVAlloc  :: KnownSymbol s =>         !t  -> FieldVal (s :# (Alloc t))

-- | The result from reading a field's value.
-- If the field is @'Mut i t'@, returns @M t@.
-- Otherwise, the result is simply the field's value.
type family ReadResult t where
  ReadResult (Immut t) = t
  ReadResult (Mut i t) = M t
  ReadResult (Alloc t) = t

-- | Compute whether or not a value is required for @'new'@.
type family Hole fd where
  Hole (Immut t) = t
  Hole (Mut NoDefault t) = t
  Hole (Mut HasDefault t) = Maybe t
  Hole (Alloc t) = Maybe t

-- | Defunctionalization symbol for @'Hole'@. This gets erased
-- by the @'Hoo.Named.Fuse'@ type family.
data HoleSym fd

-- ###########################################################
-- * Methods

-- | A method description, i.e. its type and various attributes
-- such as static/instance.
data MethodDesc = Static [Type] Type | Inst [Type] Type

-- | Allows a method to refer to the class it belongs to.
-- This is tricky without some sort of explicit knot-tying, so
-- we provide it here.
--
-- Use @'Self' 'Class'@ to refer to the enclosing class,
-- or @'Self' 'Object'@ to refer to the enclosing object's type.
data Self :: (Signature -> Type) -> Type

-- | In a method signature, polymorphic type variables should
-- be wrapped with @Poly@ to prevent @'ElimSelf'@ from getting stuck.
data Poly :: Type -> Type

type family MethodType sig spec where
  MethodType sig (Inst args ret) = Object sig -> ElimSelf sig (Func args (M ret))
  MethodType sig (Static args ret) = Class sig -> ElimSelf sig (Func args (M ret))

data MethodSym sig fd

type MethodImpl sig = Labeled (MethodSym sig)

-- | Compute a method's type from a list of its arguments and its return type.
type family Func args ret where
  Func '[] ret = ret
  Func (a ': args) ret = a -> Func args ret

-- | Structurally recurse through a type, replacing all instances
-- of @'Self' k@ with @k fs ms@. Note that this uses a rather
-- naive algorithm, and will probably miss @Self@ instances
-- inside more complicated type constructors.
type family ElimSelf (sig :: Signature) (x :: Type) :: Type where
  ElimSelf sig (Self k) = k sig
  ElimSelf sig (Class s) = Class s
  ElimSelf sig (Object s) = Object s
  ElimSelf sig (Poly s) = s
  ElimSelf sig (f a b) = f (ElimSelf sig a) (ElimSelf sig b)
  ElimSelf sig (f a) = f (ElimSelf sig a)
  ElimSelf sig a = a

-- * Odds and ends

-- | HKD-ish parameter for a Vinyl @'Rec'@.
data Labeled (f :: u -> Type) (n :: Named u) :: Type where
  (:=) :: !(Label s) -> !(Fuse u f t) -> Labeled f (s :# t)

-- | We use our own HKD family so that we can also
-- defunctionalize 'Hole' and 'MethodType'.
type family Fuse u (f :: u -> Type) (a :: u) where
  Fuse FieldDesc HoleSym a = Hole a
  Fuse MethodDesc (MethodSym sig) a = MethodType sig a
  Fuse u f a = HKD f a