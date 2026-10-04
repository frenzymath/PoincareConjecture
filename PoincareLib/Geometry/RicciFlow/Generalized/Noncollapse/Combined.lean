import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Theory
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Data
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Theory

/-! Adapted from Mapher `PoincareMT/Statements/M15Noncollapsing.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareMT

/-! The separate compact branch of Theorem 8.10. -/
structure CompactNoncollapsingConclusion : Prop where
  compact : M15CompactTheorem810.{u}

/-! Combined M15 output with independent generalized and compact constants. -/
structure NoncollapsingConclusion (n : ℕ) : Prop where
  generalized : GeneralizedNoncollapsingConclusion.{u} n
  compact : CompactNoncollapsingConclusion.{u}

end PoincareMT
