import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open MeasureTheory Set
open scoped intervalIntegral

namespace intervalIntegral




theorem forward_quotient_le_of_sub_le_integral {u f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      u t - u s ≤ ∫ r in s..t, f r)
    {t : ℝ} (ht : t ∈ Ico a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → t + h ∈ Icc a b →
      (u (t + h) - u t) / h ≤ f t + ε := by
  have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hf t ht') ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ hth
  have horder : t ≤ t + h := le_add_of_nonneg_right hh.le
  have hsub : Icc t (t + h) ⊆ Icc a b := Icc_subset_Icc ht.1 hth.2
  have hfi : IntervalIntegrable f volume t (t + h) :=
    (hf.mono (by simpa only [uIcc_of_le horder] using hsub)).intervalIntegrable
  have hi : (∫ r in t..t + h, f r) ≤ h * (f t + ε) := by
    calc
      _ ≤ ∫ _r in t..t + h, f t + ε := by
        apply integral_mono_on horder hfi intervalIntegrable_const
        intro r hr
        have hd : dist r t < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1)]
          linarith [hr.2]
        have he := hclose (hsub hr) hd
        rw [Real.dist_eq] at he
        have he' := (abs_lt.mp he).2
        linarith
      _ = h * (f t + ε) := by simp [mul_add]
  apply (div_le_iff₀ hh).mpr
  have hb := hbound t (t + h) ht' hth horder
  nlinarith

end intervalIntegral
