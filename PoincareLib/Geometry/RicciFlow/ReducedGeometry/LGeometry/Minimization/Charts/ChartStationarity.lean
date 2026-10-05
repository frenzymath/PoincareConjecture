import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Stationarity

/-! Reuse the dimension-independent variational declarations adapted from Mapher
`PoincareMT/Proofs/M08/ChartStationarity.lean`. -/

namespace PoincareMT.LGeometry

export PoincareMT.ReducedLengthMinimum.Variational
  (affine_chart_density_hasDerivAt
    affine_chart_domination_polynomial
    affine_chart_density_deriv_bound
    affine_chart_action_hasDerivAt
    chartMomentumVector
    chartForceVector
    chartMomentumVector_inner
    chartForceVector_inner
    chartMomentumVector_norm_le
    chartForceVector_norm_le
    chart_momentum_force_intervalIntegrable
    weak_momentum_of_scalar_stationarity
    weak_momentum_of_chart_stationarity)

end PoincareMT.LGeometry
