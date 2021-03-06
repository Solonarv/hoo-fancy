{-# LANGUAGE UndecidableInstances #-}
module Hoo.Operations
  ( module Hoo.Operations
  , module Hoo.Monad
  , module Hoo.MutRef
  ) where

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
import Data.Vinyl.XRec

import Hoo.Monad
import Hoo.MutRef
import Hoo.Named
import Hoo.Class

-- | Singleton record constructor. For some reason,
-- Vinyl doesn't have this in a convenient form.
rec1 :: f u -> Rec f '[u]
rec1 !x = x :& RNil

-- | Create a new instance of a class.
--
-- >>> pair <- new clsIntPair $ record (#fst := 1, #snd := 121)
new :: forall sig fs ms. (sig ~ Sig fs ms, NatToInt (RLength fs), RMap fs, RApply fs) => Class sig -> Rec (Labeled HoleSym) fs -> M (Object sig)
new cls holes = Object cls . toARec <$> fields
  where
    fields = rtraverse getCompose (rzipWith initField (clsFields cls) holes)
    initField :: forall fd. FieldInitializer sig fd -> Labeled HoleSym fd -> Compose M FieldVal fd
    initField (MustFill _) (_ := v) = Compose (pure (FVImmut v))
    initField (EmptyMut _) (_ := v) = Compose (FVMutRef <$> newRef v)
    initField (Default _ d) (_ := v) = Compose (FVMutRef <$> newRef (fromMaybe d v))
    initField (Allocate _ i) (_ := Nothing) = Compose (FVAlloc <$> i cls)
    initField (Allocate _ _) (_ := Just v) = Compose (pure (FVAlloc v))

-- | Read a field's value.
-- @
-- o #. #fld = 'deref' (obj '#' #fld)
-- @
-- >>> pair #. #fst
-- 0
infixl 9 #.
(#.) :: forall s fs ms f t. (f ~ FindNamed "field" s fs, f ~ (s :# t), NatToInt (RIndex f fs)) => Object (Sig fs ms) -> Label s -> ReadResult t
o #. l = case aget @f (objFields o) of
  FVImmut v -> v
  FVMutRef mr -> deref mr
  FVAlloc v -> v

-- | Look up the "pointer" to an object's field.
-- >>> pair # #snd
-- <a wrapped IORef Int>
infixl 9 #
(#) :: forall s t fs ms f i. (f ~ FindNamed "field" s fs, f ~ (s :# Mut i t), NatToInt (RIndex f fs)) => Object (Sig fs ms) -> Label s -> MutRef t
o # _ = case aget @f (objFields o) of FVMutRef mr -> mr

-- | Perform a (safe!) cast. You can cast an object to any class, as long
-- as every field in the class is present in the object.
as :: (IndexWitnesses (RImage fs1 fs0), NatToInt (RLength fs1)) => Object (Sig fs0 ms0) -> Class (Sig fs1 ms1) -> Object (Sig fs1 ms1)
as o0 c1 = Object c1 (rcast (objFields o0))

getClass :: Object sig -> Class sig
getClass = objClass

type RElem' r rs = RElem r rs (RIndex r rs)

-- | Overloaded @'call'@ operator.
class (s ~ NameOf m, m ~ FindNamed "method" s ms) => Call t m fs ms s x | m fs ms -> x, m -> s where
  call :: forall r. MethodType (Sig fs ms) (UnNamed m) ~ (x -> r) => t (Sig fs ms) -> Label s -> r

instance ((s :# Static args ret) ~ FindNamed "method" s ms, RElem' (s :# Static args ret) ms) => Call Class (s :# Static args ret) fs ms s (Class (Sig fs ms)) where
  call cls _ = case rget @(s :# Static args ret) (clsMethods cls) of
    _ := method -> method cls

instance Call Class (s :# Static args ret) fs ms s x => Call Object (s :# Static args ret) fs ms s x where
  call o l = call (getClass o) l

instance ((s :# Inst args ret) ~ FindNamed "method" s ms, RElem' (s :# Inst args ret) ms) => Call Object (s :# Inst args ret) fs ms s (Object (Sig fs ms)) where
  call o _ = case rget @(s :# Inst args ret) (clsMethods (objClass o)) of
    _ := method -> method o

-- | Infix alias for @'call'@, useful for methods that take no arguments.
infixl 8 .!
(.!) :: (m ~ FindNamed "method" s ms, Call t m fs ms s x, MethodType (Sig fs ms) (UnNamed m) ~ (x -> r)) => t (Sig fs ms) -> Label s -> r
(.!) = call