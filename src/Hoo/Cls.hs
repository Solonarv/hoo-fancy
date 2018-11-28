{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedLabels #-}
module Hoo.Cls where

import Data.IORef
import Data.Kind
import Data.Typeable
import GHC.TypeLits
import GHC.OverloadedLabels

import Data.Vinyl.ARec
import Data.Vinyl.Core
import Data.Vinyl.Lens
import Data.Vinyl.TypeLevel

-- | The type of classes. A class declaration looks like this:
--
-- > clsIntPair :: Class '["fst" :# Int, "snd" :# Int] '["sum" :> Method '[] Int]
-- > clsIntPair = Class (  Def 0
-- >                    :& Def 0
-- >                    :& RNil)
-- >                    (Impl (\self -> do
-- >                      l <- self #. #fst
-- >                      r <- self #. #snd
-- >                      return (l + r))
-- >                    :& RNil)
--
-- This declares a class @IntPair@, with two fields @fst :: Int@, @snd :: Int@
-- and one method, @sum :: self -> Int@, which returns the sum of @fst@ and @snd@.
data Class fs ms = Class
  { clsFields :: Rec FieldInitialVal fs
  , clsMethods :: Rec (MethodImpl fs ms) ms
  }

-- | A method description, i.e. a name and a signature.
data MethodDesc = Symbol :> MethodSig

-- | A method signature, i.e. its type.
data MethodSig = StaticMethod [Type] Type | Method [Type] Type

-- | The type of method implementations, parameterised by a
-- method description.
data MethodImpl fs ms (m :: MethodDesc) where
  Static :: KnownSymbol s
         => (Class fs ms -> Func args (M ret))
         -> MethodImpl fs ms (s :> StaticMethod args ret)
  Impl   :: KnownSymbol s
         => (CObj fs ms -> Func args (M ret))
         -> MethodImpl fs ms (s :> Method args ret)

-- | Compute a function type from a list of arguments and a
-- result type.
type family Func args ret where
  Func '[] ret = ret
  Func (a ': args) ret = a -> Func args ret

-- | The type a field descriptions; a simple pair of the field's
-- name and type.
data Fld = Symbol :# Type

-- | Extract a field's type.
type family FldType f where
  FldType (s :# t) = t

-- | Initial values for a field. This is essentially @Maybe@
-- with some extra type wrangling.
data FieldInitialVal (f :: Fld) where
  -- | No default value; the field will be initialized with an @'error'@ call.
  Nil :: KnownSymbol s => FieldInitialVal (s :# t)
  -- | @Def x@ means the field will be initialized to @x@ when creating a new
  -- object.
  Def :: KnownSymbol s => t -> FieldInitialVal (s :# t)

-- | The type of objects. Simply a reference to the class and a record of fields.
data CObj fs ms = CObj
  { cobjClass  :: Class fs ms
  , cobjFields :: ARec FieldVal fs
  }

-- | Wrapper that holds a field value.
data FieldVal f where
  FieldIORef :: KnownSymbol s => IORef t -> FieldVal (s :# t)

-- | The monad in which Hoo operations run. This is really just
-- a wrapper over @IO@, but the constructor will be hidden,
-- so arbitrary IO is not possible.
newtype M a = M { runM :: IO a }
  deriving newtype (Functor, Applicative, Monad)

-- | An abbreviation for 'new''s constraints
type WellBehaved us = ( RecApplicative us
                      , RPureConstrained (IndexableField us) us
                      , NatToInt (RLength us)
                      )

-- | Read out a field's value.
deref :: FieldVal (f :# t) -> M t
deref (FieldIORef ref) = M (readIORef ref)

-- | Create a new instance of a class. Fields that do not have a
-- default value will contain an @error@ call; do not access them
-- before setting them to a real value!
--
-- >>> pair <- new clsIntPair
new :: WellBehaved fs => Class fs ms -> M (CObj fs ms)
new cls = M $ CObj cls . toARec <$> rtraverse initField (clsFields cls)
  where
    initField :: FieldInitialVal f -> IO (FieldVal f)
    initField Nil = fmap FieldIORef . newIORef . error
        $  "uninitialized field"
    initField (Def t) = FieldIORef <$> newIORef t

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
(#.) :: forall s fs ms f t. (f ~ FindField s fs, f ~ (s :# t), NatToInt (RIndex f fs)) => CObj fs ms -> Label s -> M t
obj #. l = deref (obj # l)

-- | Look up the "pointer" to an object's field.
-- >>> pair # #snd
-- <a wrapped IORef Int>
infixl 9 #
(#) :: forall s fs ms f t. (f ~ FindField s fs, f ~ (s :# t), NatToInt (RIndex f fs)) => CObj fs ms -> Label s -> FieldVal f
o # _ = aget @f (cobjFields o)

-- | Set a field to a value.
-- >>> pair # #snd .= 42
-- >>> pair #. snd
-- 42
infix 2 .=
(.=) :: forall f. FieldVal f -> FldType f -> M ()
(FieldIORef ref) .= x = M (writeIORef ref x)

-- | Perform a (safe!) cast. You can cast an object to any class, as long
-- as every field in the class is present in the object.
as :: (IndexWitnesses (RImage fs1 fs0), NatToInt (RLength fs1)) => CObj fs0 ms0 -> Class fs1 ms1 -> CObj fs1 ms1
as o0 c1 = CObj c1 (rcast (cobjFields o0))

-- | A simple example class. It has one field, @val@, which holds a
-- single value.
clsMutBox :: forall a. Class '["val" :# a] '[]
clsMutBox = Class (Nil :& RNil) RNil

-- | A computation which creates a @'clsMutBox' @Int@
-- and sets its one field to @0@. Used for testing.
testInt :: IO (CObj '["val" :# Int] '[])
testInt = runM $ do x <- new clsMutBox; x # #val .= 0; return x