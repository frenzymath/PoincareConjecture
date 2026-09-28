import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem ContinuousOn.eq_zero_of_intervalIntegral_contDiff_smul {a b : ℝ}
    (hab : a < b) {f : ℝ → E} (hf : ContinuousOn f (Icc a b))
    (htest : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ s in a..b, ψ s • f s) = 0) :
    EqOn f 0 (Icc a b) := by
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    ((hf.mono Ioo_subset_Icc_self).locallyIntegrableOn (μ := volume) measurableSet_Ioo)
    (fun ψ hψ hψc hψs => by
      rw [← intervalIntegral.integral_eq_integral_of_support_subset
        (f := fun s => ψ s • f s)
        ((Function.support_smul_subset_left ψ f).trans
          ((subset_tsupport ψ).trans (hψs.trans Ioo_subset_Ioc_self)))]
      exact htest ψ hψ hψc hψs)
  have hrestricted : f =ᵐ[volume.restrict (Icc a b)] 0 := by
    change ∀ᵐ s ∂volume.restrict (Icc a b), f s = 0
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact hae
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hrestricted hf continuousOn_const
