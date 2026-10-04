import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.VelocityChainRules

/-! Generic variation constructions reused by the reduced-length theory. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.ReducedLength

export PoincareMT.ReducedLengthMinimum.Variation.Geometry
  (curveVelocity_congr_of_eventuallyEq curveVelocity_comp_initial_line curveVelocity_comp_square)

end PoincareMT.ReducedLength
