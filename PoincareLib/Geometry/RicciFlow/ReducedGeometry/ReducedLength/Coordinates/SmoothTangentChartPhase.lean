import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.TangentChartPhase
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.SmoothTangentChartPhase

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (tangentChartPhase_contMDiffOn)

end PoincareMT.ReducedLength
