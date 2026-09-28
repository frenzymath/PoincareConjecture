import PoincareConjecture.Proofs.M76.Mathlib.FixedNegativeCutHeightSigns

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

theorem mem_both_height_closures_of_raising_capped_image
    {S s s' d F : Set E} (H : E ≃ₜ E) (A : E → ℝ) (hA : Continuous A)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {y | A y = 0}) (hd : d ⊆ {y | A y = 0})
    (hraise : ∀ y, A y ≤ A (H y))
    (hfix : ∀ y ∈ s, A y < 0 → H y = y)
    {β γ : ℝ}
    (hsource : ∀ x ∈ S, A x ∈ Ioo (-γ) β → A x ≠ 0 →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y}))
    (hpositive : ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (0 : ℝ) β → x ∉ F →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) :
    ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 → x ∉ F →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  intro x hx hxA hxzero hxF
  rcases lt_or_gt_of_ne hxzero with hxneg | hxpos
  · obtain ⟨y, hy, hyx⟩ := hx
    have hyA : A y < 0 := (hraise y).trans_lt (by simpa only [hyx] using hxneg)
    have hys : y ∈ s := hy.resolve_right (fun hyd => hyA.ne (hd hyd))
    have hxy : x = y := hyx.symm.trans (hfix y hys hyA)
    have hxs : x ∈ s := hxy.symm ▸ hys
    obtain ⟨hlo, hhi⟩ := hsource x (hunion.subset (Or.inl hxs)) hxA hxzero
    exact H.mem_both_height_closures_of_fixed_negative_cut A hA hs' hunion
      hcut hfix hxs hxneg hlo hhi
  · exact hpositive x hx ⟨hxpos, hxA.2⟩ hxF

end Homeomorph
