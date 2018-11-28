{-# LANGUAGE UndecidableInstances #-}
module Hoo.Cls where

import Data.IORef
import Data.Kind
import Data.Typeable
import GHC.TypeLits
import GHC.OverloadedLabels

import Data.Vinyl.ARec
import Data.Vinyl.Core
import Data.Vinyl.TypeLevel

data Class fs ms = Class
  { clsFields :: Rec FieldInitialVal fs
  , clsMethods :: Rec (MethodImpl fs ms) ms
  }

data MethodSig = StaticMethod [Type] Type | Method [Type] Type

data MethodDesc = Symbol :> MethodSig

data MethodImpl fs ms (m :: MethodDesc) where
  Static :: KnownSymbol s
         => (Class fs ms -> Func args (M ret))
         -> MethodImpl fs ms (s :> StaticMethod args ret)
  Impl   :: KnownSymbol s
         => (CObj fs ms -> Func args (M ret))
         -> MethodImpl fs ms (s :> Method args ret)

type family Func args ret where
  Func '[] ret = ret
  Func (a ': args) ret = a -> Func args ret

data Fld = Symbol :# Type

data FieldInitialVal (f :: Fld) where
  Nil :: KnownSymbol s => FieldInitialVal (s :# t)
  Def :: KnownSymbol s => t -> FieldInitialVal (s :# t)

data CObj fs ms = CObj
  { cobjClass  :: Class fs ms
  , cobjFields :: ARec FieldVal fs
  }

data FieldVal f where
  FieldIORef :: KnownSymbol s => IORef t -> FieldVal (s :# t)

newtype M a = M { runM :: IO a }
  deriving newtype (Functor, Applicative, Monad)

type WellBehaved us = ( RecApplicative us
                      , RPureConstrained (IndexableField us) us
                      , NatToInt (RLength us)
                      )

deref :: FieldVal (f :# t) -> M t
deref (FieldIORef ref) = M (readIORef ref)

new :: WellBehaved fs => Class fs ms -> M (CObj fs ms)
new cls = M $ CObj cls . toARec <$> rtraverse initField (clsFields cls)
  where
    initField :: FieldInitialVal f -> IO (FieldVal f)
    initField Nil = fmap FieldIORef . newIORef . error
        $  "uninitialized field"
    initField (Def t) = FieldIORef <$> newIORef t

data Label (s :: Symbol) = Label
instance s ~ s' => IsLabel s (Label s') where fromLabel = Label

type family FieldType s fs where
  FieldType s ((s :# t) : fs) = t
  FieldType s (f : fs) = FieldType s fs
  FieldType s '[] = TypeError ('Text "No field named `" :<>: 'Text s :<>: 'Text "`.")

infix 2 #.
(#.) :: forall s fs ms f t. (t ~ FieldType s fs, f ~ (s :# t), NatToInt (RIndex f fs)) => CObj fs ms -> Label s -> M t
obj #. _ = deref (aget @(s :# t) (cobjFields obj))

infixl 9 #
(#) :: forall s fs ms f t. (t ~ FieldType s fs, f ~ (s :# t), NatToInt (RIndex f fs)) => CObj fs ms -> Label s -> FieldVal f
o # _ = aget @(s :# t) (cobjFields o)

infix 2 .=
(.=) :: forall s f t. f ~ (s :# t) => FieldVal f -> t -> M ()
(FieldIORef ref) .= x = M (writeIORef ref x)


clsPrimWrapper :: forall a. Class '["val" :# a] '[]
clsPrimWrapper = Class (Nil :& RNil) RNil

testInt :: IO (CObj '["val" :# Int] '[])
testInt = runM (new clsPrimWrapper)