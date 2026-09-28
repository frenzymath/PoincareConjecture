import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteContactEdgeVertex
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem arc_neighborhood_boundary_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A D : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype D.faces]
    (hAK : A ≤ K) (hDK : D ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    {a b : E} (hab : a ≠ b) (hcontact : A.space ∩ D.space = {a, b}) :
    (K.barycentricNeighborhood A).space ∩ D.space =
        (D.barycentricDualBlock {a}).space ∪ (D.barycentricDualBlock {b}).space ∧
      (D.barycentricDualBlock {a}).space.Nonempty ∧
      (D.barycentricDualBlock {b}).space.Nonempty ∧
      Disjoint (D.barycentricDualBlock {a}).space (D.barycentricDualBlock {b}).space := by
  classical
  have hfinite : (A.space ∩ D.space).Finite := by
    rw [hcontact]
    exact (finite_singleton b).insert a
  have ha := hcontact.symm.subset (mem_insert a {b})
  have hb := hcontact.symm.subset (mem_insert_of_mem a (mem_singleton b))
  have haV := mem_vertices_of_finite_subcomplex_intersection hAK hDK hfinite ha.1 ha.2
  have hbV := mem_vertices_of_finite_subcomplex_intersection hAK hDK hfinite hb.1 hb.2
  have hne (p : E) (hp : p ∈ D.vertices) :
      (D.barycentricDualBlock {p}).space.Nonempty := by
    refine ⟨p, (D.barycentricDualBlock {p}).vertices_subset_space ?_⟩
    refine ⟨(D.mem_barycentricSubdivision_vertices_iff p).mpr
      ⟨{p}, hp, Finset.centroid_singleton ℝ id p⟩, ?_⟩
    intro v hv
    have hvp : v = p := Finset.mem_singleton.mp hv
    subst v
    exact ⟨{p}, hp, Subset.rfl, Finset.centroid_singleton ℝ id p⟩
  have hfoot (p : E) (hp : p ∈ A.vertices) :
      (D.barycentricDualBlock {p}).space ⊆
        (K.barycentricNeighborhood A).space ∩ D.space := by
    intro x hx
    have hx' := (K.barycentricDualBlock_space_inter_subcomplex D hDK {p}).symm.subset hx
    refine ⟨?_, hx'.2⟩
    rw [K.barycentricNeighborhood_space_eq_iUnion_dualBlocks]
    exact mem_iUnion₂.mpr ⟨p, hp, hx'.1⟩
  refine ⟨?_, hne a haV.2, hne b hbV.2, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨hx, hxD⟩
      rw [K.barycentricNeighborhood_space_eq_iUnion_dualBlocks] at hx
      obtain ⟨p, hpA, hxp⟩ := mem_iUnion₂.mp hx
      have hxfoot := (K.barycentricDualBlock_space_inter_subcomplex D hDK {p}).subset
        ⟨hxp, hxD⟩
      have hpD : p ∈ D.vertices := by
        by_contra hp
        have hempty := D.barycentricDualBlock_space_eq_empty_of_not_face
          (Finset.singleton_nonempty p) hp
        rw [hempty] at hxfoot
        exact hxfoot
      have hpend := hcontact.subset
        ⟨A.vertices_subset_space hpA, D.vertices_subset_space hpD⟩
      rcases mem_insert_iff.mp hpend with rfl | hp
      · exact Or.inl hxfoot
      · obtain rfl := mem_singleton_iff.mp hp
        exact Or.inr hxfoot
    · exact union_subset (hfoot a haV.1) (hfoot b hbV.1)
  · have hnot : ({a, b} : Finset E) ∉ D.faces := by
      intro hs
      have hfinite' : (D.space ∩ A.space).Finite := by
        simpa only [inter_comm] using hfinite
      obtain ⟨p, hp, hpA⟩ := exists_edge_vertex_outside_of_finite_contact
        hDK hfull hfinite' hs (by simp [hab])
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hpA haV.1
      · exact hpA ((Finset.mem_singleton.mp hp).symm ▸ hbV.1)
    rw [disjoint_iff_inter_eq_empty, D.barycentricDualBlock_space_inter,
      Finset.singleton_union]
    exact D.barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.insert_nonempty a {b}) hnot

end Geometry.SimplicialComplex
