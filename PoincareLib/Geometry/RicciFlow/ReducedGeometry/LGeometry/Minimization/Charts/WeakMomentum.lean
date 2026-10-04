import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartRecovery
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Momentum

/-! Reuse the dimension-independent variational declarations adapted from Mapher
`PoincareMT/Proofs/M08/WeakMomentum.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variational
  (smooth_zero_integral_compact_primitive
    scalar_primitive_integration_by_parts
    weak_derivative_zero_ae_const
    primitive_integration_by_parts
    weak_momentum_primitive)

end PoincareMT.LGeometry
