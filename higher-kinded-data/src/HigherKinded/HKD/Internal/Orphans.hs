{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module HigherKinded.HKD.Internal.Orphans where

import HigherKinded.HKD.Construction
import HigherKinded.HKD.Generic

#ifdef VERSION_pretty
import Text.PrettyPrint.HughesPJClass (Pretty(..))
#endif


#ifdef VERSION_pretty
instance
    ( Pretty (f structure)
    , ConstructHKD (HKD structure hkt) structure hkt f
    )
  =>
    Pretty (HKD structure hkt f)
  where
    pPrint = pPrint . fromHKD @(HKD structure hkt) @structure @hkt @f
#endif
