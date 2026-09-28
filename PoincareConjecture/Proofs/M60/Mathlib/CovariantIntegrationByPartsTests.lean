import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos









noncomputable section

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M60

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure P} [IsLocallyFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]




theorem eqOn_zero_of_integral_contDiff_smul_eq_zero
    {T : P → E} {O : Set P} (hO : IsOpen O) (hT : ContinuousOn T O)
    (htest : ∀ ψ : P → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
      ∫ x, ψ x • T x ∂μ = 0) :
    EqOn T (fun _ => 0) O := by
  have hae := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hT.locallyIntegrableOn hO.measurableSet) htest
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hO.measurableSet).2 hae)
    hO hT continuousOn_const

end PoincareConjecture.M60
