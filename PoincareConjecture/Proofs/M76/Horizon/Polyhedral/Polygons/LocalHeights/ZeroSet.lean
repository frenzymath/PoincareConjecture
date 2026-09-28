import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Graph

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem convexHull_inter_triangleZeroSet (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3) :
    convexHull ℝ (t : Set E) ∩ K.triangleZeroSet A =
      convexHull ℝ (t : Set E) ∩ {x | A t x = 0} := by
  ext x
  constructor
  · rintro ⟨hxt, s, hs, hsc, hxs, hz⟩
    exact ⟨hxt, (hA s hs hsc t ht htc x hxs hxt).mp hz⟩
  · rintro ⟨hxt, hz⟩
    exact ⟨hxt, t, ht, htc, hxt, hz⟩

theorem triangleZeroSet_eq_preimage (K : SimplicialComplex ℝ E)
    (A : Finset E → E →ᵃ[ℝ] ℝ) {F : Type*} (f : E → F) (N : Set F)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (h : ∀ t ∈ K.faces, t.card = 3 → ∀ x ∈ convexHull ℝ (t : Set E),
      A t x = 0 ↔ f x ∈ N) :
    K.triangleZeroSet A = K.space ∩ f ⁻¹' N := by
  ext x
  constructor
  · rintro ⟨t, ht, htc, hxt, hz⟩
    exact ⟨K.convexHull_subset_space ht hxt, (h t ht htc x hxt).mp hz⟩
  · rintro ⟨hx, hfx⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, htc, hst⟩ := hpure s hs
    have hxt := convexHull_mono hst hxs
    exact ⟨t, ht, htc, hxt, (h t ht htc x hxt).mpr hfx⟩

end Geometry.SimplicialComplex
