import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.ChartPerturbationVelocity
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.CompactFieldVariation

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (exists_smooth_family_of_compact_linear_field)

end PoincareMT.ReducedLength
