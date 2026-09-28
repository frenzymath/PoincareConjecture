import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFixedSlabs
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

theorem mem_both_height_closures_of_supported_capped_cut
    {S s s' d : Set E} (H : E ≃ₜ E) (A : E → ℝ) (hA : Continuous A)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {y | A y = 0}) (hd : d ⊆ {y | A y = 0})
    {δ : ℝ} (hδ : 0 < δ) (hfix : ∀ y, δ ≤ |A y| → H y = y)
    {C : Set ℝ}
    (hsource : ∀ x ∈ S, A x ∉ C →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y})) :
    ∀ x ∈ H '' (s ∪ d), δ < |A x| → A x ∉ C →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  intro x hx hxδ hxC
  have hfixed := H.capped_image_height_band_eq (s := s) (d := d) A hδ hfix hd
    {c | δ < |c|} (fun _ hc => hc.le)
  have hxs : x ∈ s := (hfixed.subset ⟨hx, hxδ⟩).1
  have hxzero : A x ≠ 0 := by
    intro heq
    rw [heq, abs_zero] at hxδ
    exact (lt_asymm hδ hxδ).elim
  have hxnot : x ∉ s' := fun hx' => hxzero (hcut ⟨hxs, hx'⟩)
  let U := {y | δ < |A y|} ∩ s'ᶜ
  have hU : IsOpen U := (isOpen_lt continuous_const hA.abs).inter hs'.isOpen_compl
  have hxU : x ∈ U := ⟨hxδ, hxnot⟩
  have hlocal {V : Set E} (hx : x ∈ closure (S ∩ V)) :
      x ∈ closure ((H '' (s ∪ d)) ∩ V) := by
    apply closure_mono _ (hU.inter_closure ⟨hxU, hx⟩)
    intro y hy
    have hys : y ∈ s := (hunion.symm.subset hy.2.1).resolve_right hy.1.2
    exact ⟨⟨y, Or.inl hys, hfix y hy.1.1.le⟩, hy.2.2⟩
  obtain ⟨hlo, hhi⟩ := hsource x (hunion.subset (Or.inl hxs)) hxC
  exact ⟨hlocal hlo, hlocal hhi⟩

theorem finite_exceptional_height_signs_of_supported_capped_cut
    {S s s' d F : Set E} (H : E ≃ₜ E) (A : E → ℝ) (hA : Continuous A)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {y | A y = 0}) (hd : d ⊆ {y | A y = 0})
    {δ β γ : ℝ} (hδ : 0 < δ) (hδβ : δ < β) (hδγ : δ < γ)
    (hfix : ∀ y, δ ≤ |A y| → H y = y)
    {C : Set ℝ} (hC : C.Finite) (hF : F.Finite)
    (hsource : ∀ x ∈ S, A x ∉ C →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y}))
    (hlocal : ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 → x ∉ F →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) :
    (insert 0 (C ∪ A '' F)).Finite ∧
      ∀ x ∈ H '' (s ∪ d), A x ∉ insert 0 (C ∪ A '' F) →
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
          x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  refine ⟨(hC.union (hF.image A)).insert 0, ?_⟩
  intro x hx hxC
  have hxzero : A x ≠ 0 := fun heq => hxC (Or.inl heq)
  have hxold : A x ∉ C := fun h => hxC (Or.inr (Or.inl h))
  have hxF : x ∉ F := fun h => hxC (Or.inr (Or.inr ⟨x, h, rfl⟩))
  by_cases hxband : A x ∈ Ioo (-γ) β
  · exact hlocal x hx hxband hxzero hxF
  · have hxδ : δ < |A x| := by
      by_contra h
      have hbound := abs_le.mp (le_of_not_gt h)
      exact hxband ⟨by linarith [hbound.1], by linarith [hbound.2]⟩
    exact H.mem_both_height_closures_of_supported_capped_cut A hA hs' hunion
      hcut hd hδ hfix hsource x hx hxδ hxold

end Homeomorph
