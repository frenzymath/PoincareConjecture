import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteSubcomplexContact

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_edge_vertex_outside_of_finite_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K A D : SimplicialComplex ℝ E} (hAK : A ≤ K)
    (hfull : ∀ t ∈ K.faces, (∀ p ∈ t, p ∈ D.vertices) → t ∈ D.faces)
    (hfinite : (A.space ∩ D.space).Finite)
    {s : Finset E} (hs : s ∈ A.faces) (hcard : s.card = 2) :
    ∃ p ∈ s, p ∉ D.vertices := by
  classical
  by_contra h
  have hall : ∀ p ∈ s, p ∈ D.vertices := by
    intro p hp
    by_contra hpD
    exact h ⟨p, hp, hpD⟩
  have hsD : s ∈ D.faces := hfull s (hAK hs) hall
  have hsmall : MapsTo id (convexHull ℝ (s : Set E)) (A.space ∩ D.space) :=
    fun _ hx => ⟨A.convexHull_subset_space hs hx, D.convexHull_subset_space hsD hx⟩
  have hle : s.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact (convex_convexHull ℝ (s : Set E)).isPreconnected.constant_of_mapsTo
      hfinite.isDiscrete continuousOn_id hsmall
      (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy)
  omega

end Geometry.SimplicialComplex
