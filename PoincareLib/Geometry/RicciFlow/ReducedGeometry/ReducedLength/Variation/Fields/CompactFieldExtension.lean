import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Variation.Fields.ParametricFieldSum
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.ChartVelocity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.SmoothTangentChartPhase
import Mathlib.Geometry.Manifold.PartitionOfUnity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.CompactFieldExtension

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (chartVectorField_differential nonempty_parametricFieldExtensionOn_compact)

end PoincareMT.ReducedLength
