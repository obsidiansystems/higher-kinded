module HigherKinded.HKD.Internal.Exposed where



-- | Data type mainly used to inspect the tag structure of a particular higher-kinded data type.
--   Prevents overlapping instances in some case. Usually not used in end-user code.
--   (originally from 'beam-core' package)
data Exposed x
