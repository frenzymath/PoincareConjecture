import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AffineOnFaces
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FiniteFaceStarNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedSubcomplexCarriers

/-!
# Actual selected-star neighborhoods at nonzero height

A minimal containing face at nonzero height has a selected vertex
when all unselected vertex values vanish. Its whole closed star
contains a relative open neighborhood of the point. See Wall013,
sections 5 and 7, and Hudson 1969, pp. 8--10, 58--63.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

/-- Nonzero face-affine height produces a selected vertex whose
whole closed star contains an open carrier neighborhood. No ambient
dimension or ambient-interior hypothesis on the complex is used.
See Wall013, sections 5 and 7. -/
theorem exists_selected_star_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → ℝ} (hf : K.AffineOnFaces f) (A : Set E)
    (hzero : ∀ v ∈ K.vertices, v ∉ A → f v = 0)
    (x : K.space) (hx : f x ≠ 0) :
    ∃ p ∈ K.vertices, p ∈ A ∧
      ∃ V : Set K.space, IsOpen V ∧ x ∈ V ∧
        Subtype.val '' V ⊆ (K.closedStar p).space := by
  classical
  obtain ⟨s, hs, hxs, _, V, hV, hxV, hVS⟩ :=
    K.exists_minimal_faceStar_neighborhood_of_finite hK x
  have hselected : ∃ p ∈ s, p ∈ A := by
    by_contra h
    simp only [not_exists, not_and] at h
    obtain ⟨a, ha⟩ := hf s hs
    have hverts : (s : Set E) ⊆ a ⁻¹' {0} := by
      intro p hp
      change a p = 0
      rw [← ha (subset_convexHull ℝ _ hp)]
      exact hzero p (K.down_closed hs (Finset.singleton_subset_iff.mpr hp)
        (Finset.singleton_nonempty p)) (h p hp)
    have hax : a x = 0 := convexHull_min hverts
      ((convex_singleton (0 : ℝ)).affine_preimage a.toAffineMap) hxs
    exact hx ((ha hxs).trans hax)
  obtain ⟨p, hps, hpA⟩ := hselected
  have hstar : K.closedFaceStar s ≤ K.closedStar p := by
    intro t ht
    refine ⟨ht.1, K.down_closed ht.2 ?_ (Finset.insert_nonempty p t)⟩
    exact Finset.insert_subset_iff.mpr
      ⟨Finset.mem_union.mpr (Or.inl hps), Finset.subset_union_right⟩
  exact ⟨p, K.down_closed hs (Finset.singleton_subset_iff.mpr hps)
    (Finset.singleton_nonempty p), hpA, V, hV, hxV,
    hVS.trans (space_subset_of_le hstar)⟩

end Geometry.SimplicialComplex
