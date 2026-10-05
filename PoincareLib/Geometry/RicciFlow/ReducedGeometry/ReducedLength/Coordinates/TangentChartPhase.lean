import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.CurvePhase
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.TangentChartPhase

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (tangentChartPhase tangentChartPhase_continuousOn tangentChartPhase_inverse)

end PoincareMT.ReducedLength
