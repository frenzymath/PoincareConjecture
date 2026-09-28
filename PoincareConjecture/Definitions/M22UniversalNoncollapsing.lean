import PoincareConjecture.Definitions.M21AsymptoticVolume

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure UniversalNoncollapsingData where
  universal_kappa : ℝ
  universal_kappa_pos : 0 < universal_kappa

end PoincareConjecture
