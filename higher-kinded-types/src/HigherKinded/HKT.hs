{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}

module HigherKinded.HKT where

import Control.Lens
import Data.Monoid (Ap(..))
import Data.Kind
import GHC.Generics hiding (from, to)
import GHC.Generics qualified as G



class (forall x. ToHKT t f x, forall x. FromHKT t f x) => HKT t f
instance (forall x. ToHKT t f x, forall x. FromHKT t f x) => HKT t f

class FromHKT t f a where
  fromHKT' :: t f a -> f a

class ToHKT t f a where
  toHKT' :: f a -> t f a


instance FromHKT Ap f a where
  fromHKT' = getAp

instance ToHKT Ap f a where
  toHKT' = Ap



class HKT' t_f_a where
  type UnHKT t_f_a
  _HKT' :: Iso' t_f_a (UnHKT t_f_a)

instance {-# OVERLAPPABLE #-}
    ( Generic t_f_a
    , UnHKT t_f_a ~ GUnHKT (Rep t_f_a)
    , Rep t_f_a ~ (D1 d (C1 c (S1 s' (Rec0 x))))
    )
  =>
    HKT' (t_f_a :: Type)
  where
    type UnHKT t_f_a = GUnHKT (Rep t_f_a)
    _HKT' = iso G.from G.to . iso remitter reviewer
        where
          remitter (M1 (M1 (M1 (K1 x)))) = x
          reviewer x = M1 (M1 (M1 (K1 x)))

type family GUnHKT rep where
  GUnHKT (D1 d (C1 c (S1 s' (Rec0 x)))) = x
  GUnHKT (C1 c (S1 s' (Rec0 x))) = x
  GUnHKT (S1 s' (Rec0 x)) = x
  GUnHKT (Rec0 x) = x

_UnHKT' :: HKT' t_f_a => Iso' (UnHKT t_f_a) t_f_a
_UnHKT' = from _HKT'

{-# COMPLETE HKT' #-}
pattern HKT'
  :: forall t f a f_a.
     ( f_a ~$ t f a
     )
  => f a
  -> t f a
pattern HKT' unHKT <- (fromHKT' @t @f @a -> unHKT) where
  HKT' unHKT = toHKT' @t @f @a unHKT



class (IsHKT t_f_a, HKT' t_f_a, f_a ~ UnHKT t_f_a) => (~$) f_a t_f_a
instance (IsHKT t_f_a, HKT' t_f_a, f_a ~ UnHKT t_f_a) => (~$) f_a t_f_a

type family IsHKT t_f_a = r | r -> t_f_a where
  IsHKT (t f a) = (FromHKT t f a, ToHKT t f a)



{-# COMPLETE HKT #-}
pattern HKT
  :: forall t f a f_a.
     ( f_a ~$ t f a
     )
  => f a
  -> f_a
pattern HKT unHKT <- (fromHKT @t @f @a -> unHKT) where
  HKT unHKT = toHKT @t @f @a unHKT

fromHKT
  :: forall t f a f_a.
     ( f_a ~$ t f a
     )
  => f_a
  -> f a
fromHKT = fromHKT' @t @f @a . view _UnHKT'

toHKT
  :: forall t f a f_a.
     ( f_a ~$ t f a
     )
  => f a
  -> f_a
toHKT = view _HKT' . toHKT' @t @f @a



class (HKT t1 f, HKT t2 f, forall x. HKTIso' t1 t2 f x) => HKTIso t1 t2 f
instance (HKT t1 f, HKT t2 f, forall x. HKTIso' t1 t2 f x) => HKTIso t1 t2 f

class (HKT t1 f, HKT t2 f, forall f_x_1 f_x_2. (f_x_1 ~$ t1 f x, f_x_2 ~$ t2 f x) => f_x_1 ~ f_x_2) => HKTIso' t1 t2 f x
instance (HKT t1 f, HKT t2 f, forall f_x_1 f_x_2. (f_x_1 ~$ t1 f x, f_x_2 ~$ t2 f x) => f_x_1 ~ f_x_2) => HKTIso' t1 t2 f x

isoHKT
  :: forall
      t1 (t2 :: (Type -> Type) -> Type -> Type) f a f_a_1 f_a_2.
     ( f_a_1 ~$ t1 f a
     , f_a_2 ~$ t2 f a
     )
  => f_a_1
  -> f_a_2
isoHKT = toHKT @t2 @f @a . fromHKT @t1 @f @a




fmapHKT
  :: forall t f a b f_a f_b.
     ( Functor f
     , f_a ~$ t f a
     , f_b ~$ t f b
     )
  => (a -> b)
  -> f_a
  -> f_b
fmapHKT f = toHKT @t . fmap @f f . fromHKT @t

hoistHKT
  :: forall (t :: (Type -> Type) -> Type -> Type) f g a f_a g_a.
     ( f_a ~$ t f a
     , g_a ~$ t g a
     )
  => (forall x. f x -> g x)
  -> f_a
  -> g_a
hoistHKT f = toHKT @t @g @a . f . fromHKT @t @f @a

transformHKT
  :: forall (t :: (Type -> Type) -> Type -> Type) f g a b f_a g_b.
     ( f_a ~$ t f a
     , g_b ~$ t g b
     )
  => (f a -> g b)
  -> f_a
  -> g_b
transformHKT f = toHKT @t @g @b . f . fromHKT @t @f @a
