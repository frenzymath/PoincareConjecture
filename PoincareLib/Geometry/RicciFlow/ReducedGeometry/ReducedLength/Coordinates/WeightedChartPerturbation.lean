import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.ChartVelocity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.WeightedChartPerturbation

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (weightedChartPerturbation weightedChartPerturbation_eq_of_zero weightedChartPerturbation_center weightedChartPerturbation_smooth_near_center)

end PoincareMT.ReducedLength
