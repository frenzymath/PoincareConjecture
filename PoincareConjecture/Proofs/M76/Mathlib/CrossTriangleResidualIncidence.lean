import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexSlabCommonEdge

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_vertex_of_collar_trivial_section_intersection (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} {β : ℝ}
    (hreg : ∀ z ∈ K.vertices, A z ∈ Icc 0 β → z = q)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hsc : s.card = 3) (htc : t.card = 3) (hst : s ≠ t)
    {x b : E} (hxs : x ∈ convexHull ℝ (s : Set E))
    (hxt : x ∈ convexHull ℝ (t : Set E)) (hxA : A x ∈ Icc 0 β) (hbA : A b = 0)
    (hcollapse : b = q → A x = 0) (hbottom : A x = 0 → x = b)
    (hedge : ∀ e : Finset E, e.card = 2 → e ⊆ s →
      x ∈ convexHull ℝ (e : Set E) → b ∈ convexHull ℝ (e : Set E))
    (hsection : convexHull ℝ (t : Set E) ∩ {z | A z = 0} ⊆ {q}) : x = q := by
  by_cases hxq : x = q
  · exact hxq
  obtain ⟨e, he, _, hes, het, hxe, _⟩ :=
    K.common_edge_of_singleVertexSlab_intersection A hreg hs ht hsc htc hst hxs hxt hxA hxq
  have hbe : b ∈ convexHull ℝ (e : Set E) := hedge e he hes hxe
  have hbq : b = q := mem_singleton_iff.mp (hsection ⟨convexHull_mono het hbe, hbA⟩)
  exact (hbottom (hcollapse hbq)).trans hbq

theorem eq_vertex_or_top_of_collar_residual_intersection (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0) {β : ℝ}
    (hreg : ∀ z ∈ K.vertices, A z ∈ Icc 0 β → z = q)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hsc : s.card = 3) (htc : t.card = 3) (hst : s ≠ t)
    {x b : E} (hxs : x ∈ convexHull ℝ (s : Set E))
    (hxt : x ∈ convexHull ℝ (t : Set E)) (hxA : A x ∈ Icc 0 β) (hbA : A b = 0)
    (hcollapse : b = q → A x = 0) (hbottom : A x = 0 → x = b)
    (hedge : ∀ e : Finset E, e.card = 2 → e ⊆ s →
      x ∈ convexHull ℝ (e : Set E) → b ∈ convexHull ℝ (e : Set E))
    (htop : ∀ e : Finset E, e.card = 2 → e ⊆ t → q ∉ e →
      x ∈ convexHull ℝ (e : Set E) → A x = β) : x = q ∨ A x = β := by
  classical
  by_cases hxq : x = q
  · exact Or.inl hxq
  obtain ⟨e, he, _, hes, het, hxe, hAe⟩ :=
    K.common_edge_of_singleVertexSlab_intersection A hreg hs ht hsc htc hst hxs hxt hxA hxq
  by_cases hqe : q ∈ e
  · have hbe := hedge e he hes hxe
    have hbq : b = q := hAe hbe (subset_convexHull ℝ (e : Set E) hqe)
      (hbA.trans hAq.symm)
    exact Or.inl ((hbottom (hcollapse hbq)).trans hbq)
  · exact Or.inr (htop e he het hqe hxe)

end Geometry.SimplicialComplex
