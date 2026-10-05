import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.WeightedChartPerturbation
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.VelocityChainRules
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Variation.Fields.CompactFieldExtension
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartPerturbationVelocity

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (weightedChartPerturbation_curveVelocity)

end PoincareMT.ReducedLength
