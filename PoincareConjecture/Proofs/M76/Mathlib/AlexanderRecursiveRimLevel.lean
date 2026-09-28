import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabLevelCoverage

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AlexanderCollarSlab.mem_rim_of_selected_image_height_eq
    {S TY rim : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β t : ℝ}
    (M : AlexanderCollarSlab S A q β) (hTY : TY ⊆ M.collar)
    (hY : ∀ w : {w : E × ℝ | w.1 ∈ S ∩ {x | A x = 0} ∧
        w.2 ∈ Icc 0 (M.upper w.1)},
      (M.chart w : E) ∈ TY → (w : E × ℝ).1 ∈ rim)
    (f : E → E)
    (hstrict : ∀ w : {w : E × ℝ | w.1 ∈ S ∩ {x | A x = 0} ∧
        w.2 ∈ Icc 0 (M.upper w.1)},
      (w : E × ℝ).1 ∈ rim → 0 < (w : E × ℝ).2 → t < A (f (M.chart w)))
    {x : E} (hx : x ∈ TY) (hheight : A (f x) = t) : x ∈ rim := by
  let w := M.chart.symm ⟨x, hTY hx⟩
  have hw : (M.chart w : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
  have hbase := hY w (hw.symm ▸ hx)
  have hzero : (w : E × ℝ).2 = 0 := by
    apply le_antisymm _ w.property.2.1
    apply le_of_not_gt
    intro hpos
    have ht := hstrict w hbase hpos
    rw [hw, hheight] at ht
    exact lt_irrefl _ ht
  exact ((M.bottom w hzero).symm.trans hw) ▸ hbase

theorem AlexanderCollarSlab.ordinary_lower_band_eq_cap_union_remainder
    {S s d TX TY : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β t : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : s ⊆ S) (hsplit : M.collar ∩ s = TX ∪ TY)
    (H : E ≃ₜ E) (hraise : ∀ x ∈ s, A x ≤ A (H x))
    (hneg : ∀ x ∈ s, A x < 0 → H x = x)
    (hfix : ∀ x ∈ M.residual, H x = x) (ht : t ≤ β)
    (hmoved : ∀ x ∈ TY, t ≤ A (H x))
    (hrigidity : ∀ x ∈ TY, A (H x) = t → x ∈ d) :
    (H '' (s ∪ d)) ∩ {x | A x ∈ Ioc (0 : ℝ) t} =
      ((H '' d) ∪ ((H '' TX) ∪ (M.residual ∩ s))) ∩
        {x | A x ∈ Ioc (0 : ℝ) t} := by
  have hXs : TX ⊆ s :=
    (subset_union_left.trans hsplit.symm.subset).trans inter_subset_right
  ext x
  constructor
  · intro hx
    have hxTR := (image_capped_slab_level_eq hs M.cover H hraise hneg hfix
      ⟨hx.2.1, hx.2.2.trans ht⟩).subset ⟨hx.1, rfl⟩
    refine ⟨?_, hx.2⟩
    rcases hxTR.1 with hxT | hxR
    · obtain ⟨y, hyd | hyT, hyx⟩ := hxT
      · exact Or.inl ⟨y, hyd, hyx⟩
      · rcases hsplit.subset hyT with hyX | hyY
        · exact Or.inr (Or.inl ⟨y, hyX, hyx⟩)
        · have hheight : A (H y) = t :=
            le_antisymm (hyx.symm ▸ hx.2.2) (hmoved y hyY)
          exact Or.inl ⟨y, hrigidity y hyY hheight, hyx⟩
    · exact Or.inr (Or.inr hxR)
  · rintro ⟨hxD | hxX | hxR, hxA⟩
    · exact ⟨image_mono subset_union_right hxD, hxA⟩
    · exact ⟨image_mono (hXs.trans subset_union_left) hxX, hxA⟩
    · exact ⟨⟨x, Or.inl hxR.2, hfix x hxR.1⟩, hxA⟩

end Geometry
