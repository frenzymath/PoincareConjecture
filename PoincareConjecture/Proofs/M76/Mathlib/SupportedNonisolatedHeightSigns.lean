import PoincareConjecture.Proofs.M76.Mathlib.SupportedCappedHeightSigns

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

theorem nonisolated_height_signs_of_supported_capped_cut
    {S s s' d F : Set E} (H : E ≃ₜ E) (A : E → ℝ) (hA : Continuous A)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {y | A y = 0}) (hd : d ⊆ {y | A y = 0})
    {δ β γ : ℝ} (_hδ : 0 < δ) (hδβ : δ < β) (hδγ : δ < γ)
    (hfix : ∀ y, δ ≤ |A y| → H y = y)
    (hsource : ∀ x ∈ S, x ∈ closure ((S ∩ {y | A y = A x}) \ {x}) →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y}))
    (hzero : ∀ x ∈ H '' (s ∪ d), A x = 0 →
      x ∈ closure (((H '' (s ∪ d)) ∩ {y | A y = 0}) \ {x}) →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < 0}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | 0 < A y}))
    (hlocal : ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 → x ∉ F →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}))
    (hisolated : ∀ x ∈ F,
      x ∉ closure (((H '' (s ∪ d)) ∩ {y | A y = A x}) \ {x})) :
    ∀ x ∈ H '' (s ∪ d),
      x ∈ closure (((H '' (s ∪ d)) ∩ {y | A y = A x}) \ {x}) →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  intro x hx hacc
  by_cases hxzero : A x = 0
  · have hacczero : x ∈ closure (((H '' (s ∪ d)) ∩ {y | A y = 0}) \ {x}) := by
      simpa only [hxzero] using hacc
    simpa only [hxzero] using hzero x hx hxzero hacczero
  by_cases hxband : A x ∈ Ioo (-γ) β
  · exact hlocal x hx hxband hxzero (fun hxF => hisolated x hxF hacc)
  have hxδ : δ < |A x| := by
    by_contra h
    have hbound := abs_le.mp (le_of_not_gt h)
    exact hxband ⟨by linarith [hbound.1], by linarith [hbound.2]⟩
  have hlevel : (H '' (s ∪ d)) ∩ {y | A y = A x} = s ∩ {y | A y = A x} := by
    apply H.capped_image_inter_eq_of_fixedOn
      (fun y hy => hfix y (by change A y = A x at hy; rw [hy]; exact hxδ.le))
    apply disjoint_left.mpr
    intro y hyd hy
    exact hxzero (hy.symm.trans (hd hyd))
  have hxs : x ∈ s := (hlevel.subset ⟨hx, rfl⟩).1
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have hsourceAcc : x ∈ closure ((S ∩ {y | A y = A x}) \ {x}) := by
    apply closure_mono _ hacc
    intro y hy
    exact ⟨⟨hsS (hlevel.subset hy.1).1, hy.1.2⟩, hy.2⟩
  obtain ⟨hlo, hhi⟩ := hsource x (hsS hxs) hsourceAcc
  have hxnot : x ∉ s' := fun hx' => hxzero (hcut ⟨hxs, hx'⟩)
  let U := {y | δ < |A y|} ∩ s'ᶜ
  have hU : IsOpen U := (isOpen_lt continuous_const hA.abs).inter hs'.isOpen_compl
  have hxU : x ∈ U := ⟨hxδ, hxnot⟩
  have htransfer {V : Set E} (h : x ∈ closure (S ∩ V)) :
      x ∈ closure ((H '' (s ∪ d)) ∩ V) := by
    apply closure_mono _ (hU.inter_closure ⟨hxU, h⟩)
    intro y hy
    have hys : y ∈ s := (hunion.symm.subset hy.2.1).resolve_right hy.1.2
    exact ⟨⟨y, Or.inl hys, hfix y hy.1.1.le⟩, hy.2.2⟩
  exact ⟨htransfer hlo, htransfer hhi⟩

end Homeomorph
