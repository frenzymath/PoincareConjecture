import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicNonisolatedZeroSigns
import PoincareConjecture.Proofs.M76.Mathlib.RaisingCappedHeightSigns

set_option autoImplicit false

open Set

namespace Geometry.AlexanderCollarSlab

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_both_zero_height_closures_of_nonisolated
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q x : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
    (hx : x ∈ S ∩ {y | A y = 0})
    (hacc : x ∈ closure ((S ∩ {y | A y = 0}) \ {x})) :
    x ∈ closure (S ∩ {y | A y < 0}) ∧
      x ∈ closure (S ∩ {y | 0 < A y}) := by
  by_cases hxq : x = q
  · subst x
    exact (M.mem_both_zero_height_closures_of_nonisolated_apex Mneg hacc hx).symm
  · have hxneg : x ∈ S ∩ {y | (-A) y = 0} := by
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hx
    refine ⟨?_, M.mem_closure_positive_of_ne_apex hx hxq⟩
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
      Mneg.mem_closure_positive_of_ne_apex hxneg hxq

end Geometry.AlexanderCollarSlab

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

theorem not_mem_closure_punctured_level_of_cap_singleton
    {s d b : Set E} (H : E ≃ₜ E) (A : E → ℝ)
    (hs : IsClosed s) (hinter : d ∩ s ⊆ b)
    {p : E} (hp : p ∈ d \ b) {c : ℝ}
    (hsingle : (H '' d) ∩ {x | A x = c} = {H p}) :
    H p ∉ closure (((H '' (s ∪ d)) ∩ {x | A x = A (H p)}) \ {H p}) := by
  have hps : p ∉ s := fun h => hp.2 (hinter ⟨hp.1, h⟩)
  have hnot : H p ∉ H '' s := by
    rintro ⟨y, hy, hyp⟩
    exact hps ((H.injective hyp) ▸ hy)
  have hc : A (H p) = c := (hsingle.symm.subset (mem_singleton _)).2
  rw [hc]
  intro hacc
  apply hnot
  apply closure_minimal (t := H '' s) _ (H.isClosedMap _ hs) hacc
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx.1.1
  rcases hy with hys | hyd
  · exact ⟨y, hys, hyx⟩
  · exact (hx.2 (hsingle.subset ⟨⟨y, hyd, hyx⟩, hx.1.2⟩)).elim

variable [T2Space E]

theorem mem_both_zero_height_closures_of_raising_deleted_cut
    {S s s' d : Set E} (H : E ≃ₜ E) (A : E → ℝ)
    (hs' : IsClosed s') (hunion : s ∪ s' = S) (hcut : s ∩ s' ⊆ d)
    (hraise : ∀ y, A y ≤ A (H y))
    (hfix : ∀ y ∈ s, A y < 0 → H y = y)
    {x : E} (hx : x ∈ s \ d)
    (hlo : x ∈ closure (S ∩ {y | A y < 0}))
    (hhi : x ∈ closure (S ∩ {y | 0 < A y})) :
    x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < 0}) ∧
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | 0 < A y}) := by
  have hxnot : x ∉ s' := fun h => hx.2 (hcut ⟨hx.1, h⟩)
  have hlocal {V : Set E} (h : x ∈ closure (S ∩ V)) :
      x ∈ closure (s ∩ V) := by
    apply closure_mono _ (hs'.isOpen_compl.inter_closure ⟨hxnot, h⟩)
    exact fun y hy => ⟨(hunion.symm.subset hy.2.1).resolve_right hy.1, hy.2.2⟩
  have hlo' := hlocal hlo
  have hfixed : H x = x := by
    apply closure_minimal (t := {y | H y = y}) _
      (isClosed_eq H.continuous continuous_id) hlo'
    exact fun y hy => hfix y hy.1 hy.2
  refine ⟨?_, ?_⟩
  · apply closure_mono _ hlo'
    exact fun y hy => ⟨⟨y, Or.inl hy.1, hfix y hy.1 hy.2⟩, hy.2⟩
  · have himage := mem_closure_image H.continuous.continuousAt (hlocal hhi)
    rw [hfixed] at himage
    apply closure_mono _ himage
    rintro y ⟨z, hz, rfl⟩
    exact ⟨⟨z, Or.inl hz.1, rfl⟩, hz.2.trans_le (hraise z)⟩

theorem nonisolated_zero_height_signs_of_raising_deleted_cut
    {S s s' d : Set E} (H : E ≃ₜ E) (A : E → ℝ)
    (hs' : IsClosed s') (hunion : s ∪ s' = S) (hcut : s ∩ s' ⊆ d)
    (hraise : ∀ y, A y ≤ A (H y))
    (hfix : ∀ y ∈ s, A y < 0 → H y = y)
    (hzero : (H '' (s ∪ d)) ∩ {y | A y = 0} ⊆ (s ∩ {y | A y = 0}) \ d)
    (hsource : ∀ x ∈ S, x ∈ closure ((S ∩ {y | A y = A x}) \ {x}) →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y})) :
    ∀ x ∈ H '' (s ∪ d), A x = 0 →
      x ∈ closure (((H '' (s ∪ d)) ∩ {y | A y = 0}) \ {x}) →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < 0}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | 0 < A y}) := by
  intro x hx hxzero hacc
  have hxold := hzero ⟨hx, hxzero⟩
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have haccold : x ∈ closure ((S ∩ {y | A y = A x}) \ {x}) := by
    rw [hxzero]
    apply closure_mono _ hacc
    intro y hy
    have hyold := hzero hy.1
    exact ⟨⟨hsS hyold.1.1, hyold.1.2⟩, hy.2⟩
  obtain ⟨hlo, hhi⟩ := hsource x (hsS hxold.1.1) haccold
  rw [hxzero] at hlo hhi
  exact H.mem_both_zero_height_closures_of_raising_deleted_cut A hs' hunion hcut
    hraise hfix ⟨hxold.1.1, hxold.2⟩ hlo hhi

end Homeomorph
