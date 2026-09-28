import PoincareConjecture.Proofs.M14.Mathlib.FiniteEnergyDisplacement
import Mathlib.Analysis.InnerProductSpace.Calculus










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]




theorem integral_momentum_variation_eq_zero {a b : ℝ} (hab : a ≤ b)
    (P Q w : ℝ → E) (hP : ContinuousOn P (Icc a b))
    (hQ : ContinuousOn Q (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hPd : ∀ s ∈ Ioo a b, HasDerivAt P (Q s) s)
    (hwd : DifferentiableOn ℝ w (Ioo a b))
    (hd : MemLp (deriv w) 2 (volume.restrict (Icc a b))) (ha : w a = 0) (hb : w b = 0) :
    IntervalIntegrable (fun s => inner ℝ (Q s) (w s) + inner ℝ (P s) (deriv w s))
        volume a b ∧
      (∫ s in a..b, inner ℝ (Q s) (w s) + inner ℝ (P s) (deriv w s)) = 0 := by
  have hforce : IntervalIntegrable (fun s => inner ℝ (Q s) (w s)) volume a b :=
    (hQ.inner hw).intervalIntegrable_of_Icc hab
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hP
  have hspeed : Integrable (deriv w) (volume.restrict (Icc a b)) := hd.integrable (by norm_num)
  have hmomentum : IntervalIntegrable (fun s => inner ℝ (P s) (deriv w s)) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply (hspeed.norm.const_mul |C|).mono'
      ((hP.aestronglyMeasurable measurableSet_Icc).inner hd.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (norm_inner_le_norm (P s) (deriv w s)).trans
      (mul_le_mul_of_nonneg_right ((hC s hs).trans (le_abs_self C)) (norm_nonneg _))
  have hi := hforce.add hmomentum
  refine ⟨hi, ?_⟩
  have hder : ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => inner ℝ (P r) (w r))
        (inner ℝ (Q s) (w s) + inner ℝ (P s) (deriv w s)) s := by
    intro s hs
    have hdw := ((hwd s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)).hasDerivAt
    simpa only [add_comm] using (hPd s hs).inner ℝ hdw
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hP.inner hw) hder hi
  simpa only [ha, hb, inner_zero_right, sub_self] using h

end PoincareConjecture.M14
