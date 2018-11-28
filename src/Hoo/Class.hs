{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeInType #-}
module Hoo.Class where

import Data.IORef
import Data.Kind
import Data.Maybe
import Data.Typeable
import GHC.TypeLits
import GHC.OverloadedLabels

import Data.Vinyl.ARec
import Data.Vinyl.Core
import Data.Vinyl.Functor
import Data.Vinyl.Lens
import Data.Vinyl.TypeLevel
import Data.Vinyl.XRec hiding (HKD)
import qualified Data.Vinyl.XRec as Vinyl

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
data Class (sig :: Signature) where
  Class :: { clsFields :: Rec (FieldInitializer sig) (SigFields sig)
           , clsMethods :: Rec (MethodImpl sig) (SigMethods sig)
           } -> Class sig

-- | A field description, i.e. its type, mutability, and initializer type.
data FieldDesc = Immut Type
               | Mut HasDefaultVal Type
               | Alloc Type

-- | Whether a field has a default value.
data HasDefaultVal = NoDefault | HasDefault

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

-- | A class signature, i.e. a list of field and method descriptions.
data Signature = Sig [Named FieldDesc] [Named MethodDesc]

type family SigFields sig where
  SigFields (Sig fs ms) = fs

type family SigMethods sig where
  SigMethods (Sig fs ms) = ms

type HasField sig f = RElem f (SigFields sig) (RIndex f (SigFields sig))

type family MethodType sig spec where
  MethodType sig (Inst args ret) = Object sig -> ElimSelf sig (Func args (M ret))
  MethodType sig (Static args ret) = Class sig -> ElimSelf sig (Func args (M ret))

data MethodSym sig fd

type MethodImpl sig = Labeled' (MethodSym sig)

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

-- type family ElimSelves fs ms xs where
--   ElimSelves fs ms '[] = '[]
--   ElimSelves fs ms (x ': xs) = ElimSelf fs ms x ': ElimSelves fs ms xs

-- | The type of named things (e.g. methods, fields).
data Named e = Symbol :# e

-- | Strip off a named thing's name.
type family UnNamed f where
  UnNamed (s :# t) = t

-- | HKD-ish parameter for a Vinyl @'Rec'@.
data Labeled' (f :: u -> Type) (n :: Named u) :: Type where
  (:=) :: !(Label s) -> !(HKD u f t) -> Labeled' f (s :# t)

type Labeled = Labeled' Identity

-- | We use our own HKD family so that we can also
-- defunctionalize 'Hole' and 'MethodType'.
type family HKD u (f :: u -> Type) (a :: u) where
  HKD FieldDesc HoleSym a = Hole a
  HKD MethodDesc (MethodSym sig) a = MethodType sig a
  HKD u f a = Vinyl.HKD f a

-- | Initializer for a field.
data FieldInitializer sig (f :: Named FieldDesc) where
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

-- | The type of objects. Simply a reference to the class and a record of fields.
data Object (sig :: Signature) where
  Object :: { objClass  :: Class (Sig fs ms)
            , objFields :: ARec FieldVal fs
            } -> Object (Sig fs ms)

-- | Wrapper that holds a field value.
data FieldVal f where
  FVImmut  :: KnownSymbol s =>         !t  -> FieldVal (s :# (Immut t))
  FVMutRef :: KnownSymbol s => !(MutRef t) -> FieldVal (s :# (Mut i t))
  FVAlloc  :: KnownSymbol s =>         !t  -> FieldVal (s :# (Alloc t))

-- | The result from reading a field's value.
-- If the field is @'Mut i t'@, returns @'M' t@.
-- Otherwise, the result is simpe the field's value.
type family ReadResult t where
  ReadResult (Immut t) = t
  ReadResult (Mut i t) = M t
  ReadResult (Alloc t) = t

-- | A mutable reference. Internally just an @'IORef'@.
newtype MutRef a = MutRef (IORef a)

-- | Create a new mutable reference.
newRef :: a -> M (MutRef a)
newRef = M . fmap MutRef . newIORef

-- | The monad in which Hoo operations run. This is really just
-- a wrapper over @IO@, but the constructor will be hidden,
-- so arbitrary IO is not possible.
newtype M a = M { runM :: IO a }
  deriving newtype (Functor, Applicative, Monad)

-- | Read out a mutable reference's value
deref :: MutRef a -> M a
deref (MutRef ref) = M (readIORef ref)

-- | Singleton record constructor. For some reason,
-- Vinyl doesn't have this in a convenient form.
rec1 :: f u -> Rec f '[u]
rec1 !x = x :& RNil

-- | Compute whether or not a value is required for @'new'@.
type family Hole fd where
  Hole (Immut t) = t
  Hole (Mut NoDefault t) = t
  Hole (Mut HasDefault t) = Maybe t
  Hole (Alloc t) = Maybe t

-- | Defunctionalization symbol for @'Hole'@. This gets erased
-- by the @'HKD'@ type family.
data HoleSym fd

-- | Create a new instance of a class.
--
-- >>> pair <- new clsIntPair $ record (#fst := 1, #snd := 121)
new :: forall sig fs ms. (sig ~ Sig fs ms, NatToInt (RLength fs), RMap fs, RApply fs) => Class sig -> Rec (Labeled' HoleSym) fs -> M (Object sig)
new cls holes = Object cls . toARec <$> fields
  where
    fields = rtraverse getCompose (rzipWith initField (clsFields cls) holes)
    initField :: forall fd. FieldInitializer sig fd -> Labeled' HoleSym fd -> Compose M FieldVal fd
    initField (MustFill _) (_ := v) = Compose (pure (FVImmut v))
    initField (EmptyMut _) (_ := v) = Compose (FVMutRef <$> newRef v)
    initField (Default _ d) (_ := v) = Compose (FVMutRef <$> newRef (fromMaybe d v))
    initField (Allocate _ i) (_ := Nothing) = Compose (FVAlloc <$> i cls)
    initField (Allocate _ _) (_ := Just v) = Compose (pure (FVAlloc v))


-- | A specialised @'Proxy'@, used for carrying field names.
data Label (s :: Symbol) = Label
instance s ~ s' => IsLabel s (Label s') where fromLabel = Label

-- | Extract a field's type by its name. Will fail with a nice error
-- message if the field cannot be found.
type family FindField s fs where
  FindField s ((s :# t) : fs) = (s :# t)
  FindField s (f : fs) = FindField s fs
  FindField s '[] = TypeError ('Text "No field named " :<>: 'ShowType s :<>: 'Text ".")

-- | Read a field's value.
-- @
-- o #. #fld = 'deref' (obj '#' #fld)
-- @
-- >>> pair #. #fst
-- 0
infix 2 #.
(#.) :: forall s fs ms f t. (f ~ FindField s fs, f ~ (s :# t), NatToInt (RIndex f fs)) => Object (Sig fs ms) -> Label s -> ReadResult t
o #. l = case aget @f (objFields o) of
  FVImmut v -> v
  FVMutRef mr -> deref mr
  FVAlloc v -> v

-- | Look up the "pointer" to an object's field.
-- >>> pair # #snd
-- <a wrapped IORef Int>
infixl 9 #
(#) :: forall s t fs ms f i. (f ~ FindField s fs, f ~ (s :# Mut i t), NatToInt (RIndex f fs)) => Object (Sig fs ms) -> Label s -> MutRef t
o # _ = case aget @f (objFields o) of FVMutRef mr -> mr

-- | Set a mutable reference's value.
-- >>> pair # #snd #= 42
-- >>> pair #. snd
-- 42
infix 2 #=
(#=) :: forall f s t i. MutRef t -> t -> M ()
(MutRef ref) #= x = M (writeIORef ref x)

-- | Perform a (safe!) cast. You can cast an object to any class, as long
-- as every field in the class is present in the object.
as :: (IndexWitnesses (RImage fs1 fs0), NatToInt (RLength fs1)) => Object (Sig fs0 ms0) -> Class (Sig fs1 ms1) -> Object (Sig fs1 ms1)
as o0 c1 = Object c1 (rcast (objFields o0))

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
                         '[ "mempty" :# Static '[] (Poly a)
                          , "mappend" :# Static '[Poly a, Poly a] (Poly a)
                          , "eat" :# Inst '[Poly a] (Poly a)
                          , "of" :# Static '[Poly a] (Self Object)
                          , "unwrap" :# Inst '[] (Poly a)
                          ]
