import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem IsFinitePL.preimage_ballPair {s : Set E} {t a b : Set F}
    {e : s ≃ₜ t} (he : e.IsFinitePL) (ha : IsFinitePLBallPair V a b)
    (hat : a ⊆ t) {f : E → F} (hf : ∀ x : s, (e x : F) = f x) :
    IsFinitePLBallPair V (s ∩ f ⁻¹' a) (s ∩ f ⁻¹' b) := by
  obtain ⟨g, hg, hge⟩ := he.symm
  have hginj : InjOn g t := by
    intro x hx y hy hxy
    have h : e.symm ⟨x, hx⟩ = e.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hge] using hxy
    exact congrArg Subtype.val (e.symm.injective h)
  have himage (c : Set F) (hc : c ⊆ t) : g '' c = s ∩ f ⁻¹' c := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hmem : g y ∈ s := hge ⟨y, hc hy⟩ ▸ (e.symm ⟨y, hc hy⟩).property
      refine ⟨hmem, ?_⟩
      have heq : e.symm ⟨y, hc hy⟩ = ⟨g y, hmem⟩ := Subtype.ext (hge _)
      have hyf : f (g y) = y := by
        rw [← hf ⟨g y, hmem⟩, ← heq, e.apply_symm_apply]
      change f (g y) ∈ c
      rw [hyf]
      exact hy
    · rintro ⟨hxs, hfx⟩
      refine ⟨f x, hfx, ?_⟩
      have hfxmem : f x ∈ t := hc hfx
      rw [← hge ⟨f x, hfxmem⟩]
      have heq : (⟨f x, hfxmem⟩ : t) = e ⟨x, hxs⟩ :=
        Subtype.ext (hf ⟨x, hxs⟩).symm
      rw [heq, e.symm_apply_apply]
  have h := ha.image_of_subset hg hat hginj
  rw [himage a hat, himage b (ha.1.trans hat)] at h
  exact h

end Homeomorph
