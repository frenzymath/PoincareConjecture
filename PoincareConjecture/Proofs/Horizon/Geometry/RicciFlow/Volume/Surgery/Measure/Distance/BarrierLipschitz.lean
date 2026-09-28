import PoincareConjecture.Proofs.M10.BarrierLipschitz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.AffineMap

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace PoincareConjecture.SurgeryVolume.Measure

theorem frequently_slope_lt_of_upper_support {f g : ℝ → ℝ} {x d r : ℝ}
    (hg : HasDerivAt g d x) (heq : g x = f x)
    (hle : ∀ᶠ y in 𝓝 x, f y ≤ g y) (hdr : d < r) :
    ∃ᶠ y in 𝓝[>] x, slope f x y < r := by
  have hs := hg.hasDerivWithinAt.limsup_slope_le' (s := Ioi x) (lt_irrefl x) hdr
  have hnear : ∀ᶠ y in 𝓝[>] x, f y ≤ g y := nhdsWithin_le_nhds hle
  apply Filter.Eventually.frequently
  filter_upwards [hs, hnear, self_mem_nhdsWithin] with y hys hy hxy
  apply lt_of_le_of_lt _ hys
  rw [slope_def_field, slope_def_field, heq]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hy _) (sub_pos.mpr hxy).le

set_option backward.isDefEq.respectTransparency false in

theorem sub_le_mul_of_upper_supports {f : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ x ∈ Ico a b, ∃ g : ℝ → ℝ, ∃ d : ℝ,
      HasDerivAt g d x ∧ g x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ g y) ∧ d ≤ C) :
    f b - f a ≤ C * (b - a) := by
  have hcomparison : ∀ x ∈ Icc a b, f x ≤ f a + C * (x - a) := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hf
      (B' := fun _ ↦ C)
    · simp
    · fun_prop
    · intro x _
      simpa only [mul_one, id_eq] using
        ((((hasDerivAt_id x).sub_const a).const_mul C).const_add (f a)).hasDerivWithinAt
    · intro x hx r hr
      obtain ⟨g, d, hd, heq, hle, hC⟩ := hsupport x hx
      exact frequently_slope_lt_of_upper_support hd heq hle (hC.trans_lt hr)
  exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hcomparison b ⟨hab, le_rfl⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sub_le_norm_of_upper_supports {S : Set E} (hS : Convex ℝ S)
    {f : E → ℝ} (hf : ContinuousOn f S) {C : ℝ}
    (hsupport : ∀ z ∈ S, ∃ g : E → ℝ, ∃ L : E →L[ℝ] ℝ,
      HasFDerivAt g L z ∧ g z = f z ∧
        (∀ᶠ w in 𝓝 z, f w ≤ g w) ∧ ‖L‖ ≤ C)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    f y - f x ≤ C * ‖y - x‖ := by
  let c : ℝ → E := AffineMap.lineMap x y
  have hc : Continuous c := AffineMap.lineMap_continuous
  have hcS : MapsTo c (Icc 0 1) S := fun _ ht ↦ hS.lineMap_mem hx hy ht
  have hseg := sub_le_mul_of_upper_supports (f := f ∘ c) (C := C * ‖y - x‖)
    zero_le_one (hf.comp hc.continuousOn hcS) (fun t ht ↦ ?_)
  · simpa only [Function.comp_apply, c, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, sub_zero, mul_one] using hseg
  obtain ⟨g, L, hL, heq, hdom, hbound⟩ := hsupport (c t) (hcS (Ico_subset_Icc_self ht))
  refine ⟨g ∘ c, L (y - x),
    hL.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap, heq,
    hc.continuousAt hdom, ?_⟩
  exact (le_abs_self _).trans ((L.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)))

theorem lipschitzOnWith_of_upper_supports {S : Set E} (hS : Convex ℝ S)
    {f : E → ℝ} (hf : ContinuousOn f S) {C : ℝ≥0}
    (hsupport : ∀ z ∈ S, ∃ g : E → ℝ, ∃ L : E →L[ℝ] ℝ,
      HasFDerivAt g L z ∧ g z = f z ∧
        (∀ᶠ w in 𝓝 z, f w ≤ g w) ∧ ‖L‖ ≤ C) :
    LipschitzOnWith C f S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := sub_le_norm_of_upper_supports hS hf hsupport hx hy
    rw [norm_sub_rev] at h
    linarith
  · exact sub_le_norm_of_upper_supports hS hf hsupport hy hx

end PoincareConjecture.SurgeryVolume.Measure
