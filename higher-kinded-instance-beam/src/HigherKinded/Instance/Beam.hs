{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module HigherKinded.Instance.Beam
  ( module HigherKinded.Instance.Beam
  , Columnar
  , Columnar'
  ) where


import Data.Functor.Identity
import Data.Kind
--import Data.Some
import Database.Beam.Schema.Tables as Beam
import GHC.Generics (Generic)

import HigherKinded.HKT
import HigherKinded.HKD



type Beamed structure = HKD structure Beam'

pattern Beamed
  :: forall structure f.
     Construct (Beamed structure) structure f
  => f structure
  -> Beamed structure f
pattern Beamed { unBeamed } <- (fromHKD @(Beamed structure) @structure @f -> unBeamed) where
  Beamed x = toHKD @(Beamed structure) @structure @f x


#if MIN_VERSION_beam_core(0,10,3)
instance BeamableHKD structure Beam' => Beamable (Beamed structure)

class
    ( GTableSkeleton (HKD_ structure Beam' Ignored)
    , forall f g h. GZipTablesHKD structure Beam' f g h
    )
  => BeamableHKD structure hkt

instance
    ( GTableSkeleton (HKD_ structure Beam' Ignored)
    , forall f g h. GZipTablesHKD structure Beam' f g h
    )
  => BeamableHKD structure hkt

class
    ( GZipTables f g h
        (HKD_ structure hkt Beam.Exposed)
        (HKD_ structure hkt f)
        (HKD_ structure hkt g)
        (HKD_ structure hkt h)
    , GenericHKD' structure hkt f
    , GenericHKD' structure hkt g
    , GenericHKD' structure hkt h
    )
  => GZipTablesHKD structure hkt f g h

instance
    ( GZipTables f g h
        (HKD_ structure hkt Beam.Exposed)
        (HKD_ structure hkt f)
        (HKD_ structure hkt g)
        (HKD_ structure hkt h)
    , GenericHKD' structure hkt f
    , GenericHKD' structure hkt g
    , GenericHKD' structure hkt h
    )
  => GZipTablesHKD structure hkt f g h
#endif



bitraverseBeamed
  :: forall structure f g h t.
     ( Applicative t
     , BiTraversableHKD (Beamed structure) Beam' f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> Beamed structure f
  -> Beamed structure g
  -> t (Beamed structure h)
bitraverseBeamed = bitraverseBeam @(Beamed structure) @f @g @h

zipBeamed
  :: forall structure f g h.
     ( ZippableHKD (Beamed structure) Beam' f g h
     )
  => (forall a. f a -> g a -> h a)
  -> Beamed structure f
  -> Beamed structure g
  -> Beamed structure h
zipBeamed = zipBeam @(Beamed structure) @f @g @h

traverseBeamed
  :: forall structure f g t.
     ( Applicative t
     , TraversableHKD (Beamed structure) Beam' f g
     )
  => (forall x. f x -> t (g x))
  -> Beamed structure f
  -> t (Beamed structure g)
traverseBeamed = traverseBeam @(Beamed structure) @f @g

mapBeamed
  :: forall structure f g.
     ( FunctorHKD (Beamed structure) Beam' f g
     )
  => (forall x. f x -> g x)
  -> Beamed structure f
  -> Beamed structure g
mapBeamed = mapBeam @(Beamed structure) @f @g

pureBeamed
  :: forall structure f.
     ( FunctorHKD (Beamed structure) Beam' f f
     )
  => (forall a. f a)
  -> Beamed structure f
pureBeamed = pureBeam @(Beamed structure) @f



type Beam :: (Type -> Type) -> Type -> Type
type family Beam f a where
  --Beam f (Some t) = t f
  Beam f a = Columnar f a


newtype Beam' f a = Beam' { unBeam' :: Beam f a }
  deriving stock (Generic)


--instance (Construct t (t Identity) f, Functor f) => FromHKT Beam' f (Some (t :: (Type -> Type) -> Type)) where
--  fromHKT' (Beam' t) = Some @t @Identity <$> fromHKD t
--
--instance (forall f. Construct t (t f) Identity) => ToHKT Beam' Identity (Some (t :: (Type -> Type) -> Type)) where
--  toHKT' (Identity s) = Beam' $ foldSome (toHKD . Identity) s


instance {-# OVERLAPPABLE #-} (Beam f a ~ Columnar f a, FromHKT Columnar' f a) => FromHKT Beam' f a where
  fromHKT' = fromHKT' @Columnar' @f @a . Columnar' . unBeam'

instance {-# OVERLAPPABLE #-} (Beam f a ~ Columnar f a, ToHKT Columnar' f a) => ToHKT Beam' f a where
  toHKT' = Beam' . unColumnar' . toHKT' @Columnar' @f @a


pattern Beam
  :: forall f a f_a.
     ( f_a ~$ Beam' f a
     )
  => f a
  -> f_a
pattern Beam { unBeam } <- (fromBeam @f @a -> unBeam) where
  Beam f_a = toBeam @f @a f_a

fromBeam
  :: forall f a f_a.
     ( f_a ~$ Beam' f a
     )
  => f_a
  -> f a
fromBeam = fromHKT @Beam' @f @a

toBeam
  :: forall f a f_a.
     ( f_a ~$ Beam' f a
     )
  => f a
  -> f_a
toBeam = toHKT @Beam' @f @a



fmapBeam
  :: forall x y f f_x f_y.
     ( Functor f
     , f_x ~$ Beam' f x
     , f_y ~$ Beam' f y
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapBeam = fmapHKT @Beam' @f @x @y

hoistBeam
  :: forall
       x
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_x.
     ( f_x ~$ Beam' f x
     , g_x ~$ Beam' g x
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistBeam = hoistHKT @Beam' @f @g @x

transformBeam
  :: forall
       x y
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_y.
     ( f_x ~$ Beam' f x
     , g_y ~$ Beam' g y
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformBeam = transformHKT @Beam' @f @g @x @y



bitraverseBeam
  :: forall hkd f g h t.
     ( Applicative t
     , BiTraversableHKD hkd Beam' f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> hkd f
  -> hkd g
  -> t (hkd h)
bitraverseBeam = bitraverseHKD @hkd @Beam' @f @g @h

zipBeam
  :: forall hkd f g h.
     ( ZippableHKD hkd Beam' f g h
     )
  => (forall a. f a -> g a -> h a)
  -> hkd f
  -> hkd g
  -> hkd h
zipBeam = zipHKD @hkd @Beam' @f @g @h

traverseBeam
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Beam' f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseBeam = traverseHKD @hkd @Beam' @f @g

mapBeam
  :: forall hkd f g.
     ( FunctorHKD hkd Beam' f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapBeam = mapHKD @hkd @Beam' @f @g

pureBeam
  :: forall hkd f.
     ( FunctorHKD hkd Beam' f f
     )
  => (forall a. f a)
  -> hkd f
pureBeam = pureHKD @hkd @Beam' @f



transformBeam'
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Beam' f g
     , f_hkd_f ~$ Beam' f (hkd f)
     , f_hkd_g ~$ Beam' f (hkd g)
     , g_hkd_g ~$ Beam' g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformBeam' = transformHKD @hkd @Beam' @Beam' @f @g @f_hkd_f @f_hkd_g @g_hkd_g



deriving stock instance (Generic (Columnar' f a))

unColumnar' :: Columnar' f a -> Columnar f a
unColumnar' (Columnar' x) = x


instance FromHKT Columnar' Identity a where
  fromHKT' (Columnar' a) = Identity a

instance {-# OVERLAPPABLE #-} (Columnar f a ~ f a) => FromHKT Columnar' f a where
  fromHKT' (Columnar' a) = a


instance ToHKT Columnar' Identity a where
  toHKT' (Identity a) = Columnar' a

instance {-# OVERLAPPABLE #-} (Columnar f a ~ f a) => ToHKT Columnar' f a where
  toHKT' = Columnar'


instance
    ( Functor f
    , HKT Columnar' f
    )
  =>
    Functor (Columnar' f)
  where
    fmap f = toHKT' . fmap f . fromHKT' @_ @f


instance {-# OVERLAPPING #-} (Beamable hkd, HKT Columnar' f, HKT Columnar' g, HKT Columnar' h) => BiTraversableHKD hkd Columnar' f g h where
  bitraverseHKD combine f g =
    zipBeamFieldsM
      (\(f' :: Columnar' f a)
        (g' :: Columnar' g a)
      -> fmap (toHKT' @Columnar' @h @a) $ combine (fromHKT' @Columnar' @f @a f') (fromHKT' @Columnar' @g @a g')
      ) f g



pattern Columnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f a
  -> f_a
pattern Columnar { unColumnar } <- (fromColumnar @f @a -> unColumnar) where
  Columnar f_a = toColumnar @f @a f_a

fromColumnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f_a
  -> f a
fromColumnar = fromHKT @Columnar' @f @a

toColumnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f a
  -> f_a
toColumnar = toHKT @Columnar' @f @a



fmapColumnar
  :: forall x y f f_x f_y.
     ( Functor f
     , f_x ~$ Columnar' f x
     , f_y ~$ Columnar' f y
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapColumnar = fmapHKT @Columnar' @f @x @y

hoistColumnar
  :: forall
       x
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_x.
     ( f_x ~$ Columnar' f x
     , g_x ~$ Columnar' g x
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistColumnar = hoistHKT @Columnar' @f @g @x

transformColumnar
  :: forall
       x y
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_y.
     ( f_x ~$ Columnar' f x
     , g_y ~$ Columnar' g y
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformColumnar = transformHKT @Columnar' @f @g @x @y



bitraverseColumnar
  :: forall hkd f g h t.
     ( Applicative t
     , BiTraversableHKD hkd Columnar' f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> hkd f
  -> hkd g
  -> t (hkd h)
bitraverseColumnar = bitraverseHKD @hkd @Columnar' @f @g @h

zipColumnar
  :: forall hkd f g h.
     ( ZippableHKD hkd Columnar' f g h
     )
  => (forall a. f a -> g a -> h a)
  -> hkd f
  -> hkd g
  -> hkd h
zipColumnar = zipHKD @hkd @Columnar' @f @g @h

traverseColumnar
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Columnar' f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseColumnar = traverseHKD @hkd @Columnar' @f @g

mapColumnar
  :: forall hkd f g.
     ( FunctorHKD hkd Columnar' f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapColumnar = mapHKD @hkd @Columnar' @f @g

pureColumnar
  :: forall hkd f.
     ( FunctorHKD hkd Columnar' f f
     )
  => (forall a. f a)
  -> hkd f
pureColumnar = pureHKD @hkd @Columnar' @f



transformColumnar'
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Columnar' f g
     , f_hkd_f ~$ Columnar' f (hkd f)
     , f_hkd_g ~$ Columnar' f (hkd g)
     , g_hkd_g ~$ Columnar' g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformColumnar' = transformHKD @hkd @Columnar' @Columnar' @f @g @f_hkd_f @f_hkd_g @g_hkd_g
