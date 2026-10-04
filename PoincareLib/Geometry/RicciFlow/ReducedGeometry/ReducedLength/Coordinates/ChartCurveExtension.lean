import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Variation.Fields.ChartVectorField
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartCurveExtension

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (chartVectorField_param_smooth curveVelocityWithin_inverseChart chartCurveVelocityExtension chartCurveVelocityExtension_pullback)

end PoincareMT.ReducedLength
