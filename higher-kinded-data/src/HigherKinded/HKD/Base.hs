{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module HigherKinded.HKD.Base
  ( module HigherKinded.HKD.Base
  , module HigherKinded.HKT.Base
  ) where

import HigherKinded.HKD.Class
import HigherKinded.HKD.Construction
import HigherKinded.HKD.Generic
import HigherKinded.HKT
import HigherKinded.HKT.Base



type (|>) structure = HKD structure Applied

type F structure = (|>) structure

pattern F
  :: forall structure f.
     ConstructHKD (F structure) structure Applied f
  => f structure
  -> F structure f
pattern F { unF } <- (fromHKD @(F structure) @structure @Applied @f -> unF) where
  F x = toHKD @(F structure) @structure @Applied @f x



bitraverseF
  :: forall structure f g h t.
     ( Applicative t
     , BiTraversableHKD (F structure) Applied f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> structure |> f
  -> structure |> g
  -> t (structure |> h)
bitraverseF = bitraverseApp @(F structure) @f @g @h

zipF
  :: forall structure f g h.
     ( ZippableHKD (F structure) Applied f g h
     )
  => (forall a. f a -> g a -> h a)
  -> structure |> f
  -> structure |> g
  -> structure |> h
zipF = zipApp @(F structure) @f @g @h

traverseF
  :: forall structure f g t.
     ( Applicative t
     , TraversableHKD (F structure) Applied f g
     )
  => (forall x. f x -> t (g x))
  -> structure |> f
  -> t (structure |> g)
traverseF = traverseApp @(F structure) @f @g

mapF
  :: forall structure f g.
     ( FunctorHKD (F structure) Applied f g
     )
  => (forall x. f x -> g x)
  -> structure |> f
  -> structure |> g
mapF = mapApp @(F structure) @f @g

pureF
  :: forall structure f.
     ( FunctorHKD (F structure) Applied f f
     )
  => (forall a. f a)
  -> structure |> f
pureF = pureApp @(F structure) @f



bitraverseApp
  :: forall hkd f g h t.
     ( Applicative t
     , BiTraversableHKD hkd Applied f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> hkd f
  -> hkd g
  -> t (hkd h)
bitraverseApp = bitraverseHKD @hkd @Applied @f @g @h

zipApp
  :: forall hkd f g h.
     ( ZippableHKD hkd Applied f g h
     )
  => (forall a. f a -> g a -> h a)
  -> hkd f
  -> hkd g
  -> hkd h
zipApp = zipHKD @hkd @Applied @f @g @h

traverseApp
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Applied f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseApp = traverseHKD @hkd @Applied @f @g

mapApp
  :: forall hkd f g.
     ( FunctorHKD hkd Applied f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapApp = mapHKD @hkd @Applied @f @g

pureApp
  :: forall hkd f.
     ( FunctorHKD hkd Applied f f
     )
  => (forall a. f a)
  -> hkd f
pureApp = pureHKD @hkd @Applied @f



transformApplied
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Applied f g
     , f_hkd_f ~$ Applied f (hkd f)
     , f_hkd_g ~$ Applied f (hkd g)
     , g_hkd_g ~$ Applied g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformApplied = transformHKD @hkd @Applied @Applied @f @g @f_hkd_f @f_hkd_g @g_hkd_g
