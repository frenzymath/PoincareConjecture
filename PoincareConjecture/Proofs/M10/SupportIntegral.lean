import PoincareConjecture.Proofs.M10.BarrierLipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M10

theorem image_le_of_upper_supports {f B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivAt B (B' x) x)
    (ha : f a ≤ B a)
    (hsupport : ∀ x ∈ Ico a b, ∃ g : ℝ → ℝ, ∃ d : ℝ,
      HasDerivAt g d x ∧ g x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ g y) ∧ d ≤ B' x) :
    ∀ x ∈ Icc a b, f x ≤ B x := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB
    (fun x hx ↦ (hB' x hx).hasDerivWithinAt)
  intro x hx r hr
  obtain ⟨g, d, hd, heq, hdom, hbound⟩ := hsupport x hx
  exact frequently_slope_lt_of_upper_support hd heq hdom (hbound.trans_lt hr)

theorem sub_le_integral_of_upper_supports {f h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hh : Continuous h)
    (hsupport : ∀ x ∈ Ico a b, ∃ g : ℝ → ℝ, ∃ d : ℝ,
      HasDerivAt g d x ∧ g x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ g y) ∧ d ≤ h x) :
    f b - f a ≤ ∫ x in a..b, h x := by
  let B : ℝ → ℝ := fun t ↦ f a + ∫ x in a..t, h x
  have hB : ∀ t, HasDerivAt B (h t) t := fun t ↦
    (intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable a t)
      hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt).const_add _
  have hBa : f a ≤ B a := by simp [B]
  have hcomp := image_le_of_upper_supports hf
    (fun t _ ↦ (hB t).continuousAt.continuousWithinAt) (fun t _ ↦ hB t) hBa hsupport
      b ⟨hab, le_rfl⟩
  exact sub_le_iff_le_add.mpr (by simpa only [B, add_comm] using hcomp)

end PoincareConjecture.M10
