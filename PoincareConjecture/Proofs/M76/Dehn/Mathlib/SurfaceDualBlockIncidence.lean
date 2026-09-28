import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualContact
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSurfaceIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

omit [DecidableEq E] in

theorem iUnion_vertex_dualBlocks_space :
    (⋃ p ∈ K.vertices, (K.barycentricDualBlock {p}).space) = K.space := by
  rw [← K.barycentricNeighborhood_space_eq_iUnion_dualBlocks K]
  apply Subset.antisymm
  · exact (space_subset_of_le (K.barycentricNeighborhood_le K)).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  · exact K.space_subset_barycentricNeighborhood (L := K) le_rfl

omit [DecidableEq E] in

theorem barycentricDualBlock_space_eq_centroid_of_maximal
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s) :
    (K.barycentricDualBlock s).space = {s.centroid ℝ id} := by
  simpa only [inter_self] using K.dualBlocks_inter_eq_centroid_of_no_common_coface
    K K le_rfl le_rfl hs hs (fun t ht _ hst => hmax t ht hst)

theorem vertex_dualBlocks_space_inter (p q : E) :
    (K.barycentricDualBlock {p}).space ∩ (K.barycentricDualBlock {q}).space =
      (K.barycentricDualBlock {p, q}).space := by
  simpa only [Finset.singleton_union] using K.barycentricDualBlock_space_inter {p} {q}

theorem dualEdge_space_subset_vertex_links {p q : E}
    (hp : p ∈ K.vertices) (hq : q ∈ K.vertices) (hpq : p ≠ q) :
    (K.barycentricDualBlock {p, q}).space ⊆
      (K.barycentricSubdivision.link p).space ∩
        (K.barycentricSubdivision.link q).space := by
  rw [← K.vertex_dualBlocks_space_inter p q,
    K.barycentricDualBlock_singleton_eq_closedStar hp,
    K.barycentricDualBlock_singleton_eq_closedStar hq]
  exact K.barycentric_closedStars_inter_subset_links hp hq hpq

theorem barycentric_vertex_link_space_eq_iUnion_dualEdges
    {p : E} (hp : p ∈ K.vertices) :
    (K.barycentricSubdivision.link p).space =
      ⋃ q ∈ {q : E | q ≠ p ∧ ({p, q} : Finset E) ∈ K.faces},
        (K.barycentricDualBlock {p, q}).space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨f, hf, hxf⟩ := mem_space_iff.mp hx
    have hstar : f ∈ (K.barycentricSubdivision.closedStar p).faces :=
      ⟨hf.1, hf.2.2⟩
    have hdual : f ∈ (K.barycentricDualBlock {p}).faces := by
      rwa [K.barycentricDualBlock_singleton_eq_closedStar hp]
    obtain ⟨a, ha, hfaces, hchain, hfa⟩ :=
      (K.barycentricSubdivision_faces_of_face_chains f).mp hf.1
    have hpa (t : Finset E) (ht : t ∈ a) : p ∈ t := by
      have hct : t.centroid ℝ id ∈ f :=
        hfa.symm ▸ Finset.mem_image.mpr ⟨t, ht, rfl⟩
      obtain ⟨u, hu, hpu, hut⟩ := hdual.2 _ hct
      have he : (⟨u, hu⟩ : K.faces) = ⟨t, hfaces t ht⟩ :=
        K.faceCentroid_injective hut
      have hut' : u = t := congrArg Subtype.val he
      rw [← hut']
      exact hpu (Finset.mem_singleton_self p)
    obtain ⟨s, hs, hmin⟩ := a.exists_min_image Finset.card ha
    have hst (t : Finset E) (ht : t ∈ a) : s ⊆ t := by
      rcases hchain s hs t ht with h | h
      · exact h
      · exact (Finset.eq_of_subset_of_card_le h (hmin t ht)).symm.subset
    have hnsub : ¬s ⊆ ({p} : Finset E) := by
      intro hsub
      have heq : s = {p} := Finset.Subset.antisymm hsub
        (Finset.singleton_subset_iff.mpr (hpa s hs))
      apply hf.2.1
      have hcs : s.centroid ℝ id ∈ f :=
        hfa.symm ▸ Finset.mem_image.mpr ⟨s, hs, rfl⟩
      simpa only [heq, Finset.centroid_singleton, id_eq] using hcs
    obtain ⟨q, hqs, hqp⟩ := Finset.not_subset.mp hnsub
    have hqp' : q ≠ p := by simpa only [Finset.mem_singleton] using hqp
    have hedge : ({p, q} : Finset E) ∈ K.faces :=
      K.down_closed (hfaces s hs)
        (Finset.insert_subset (hpa s hs) (Finset.singleton_subset_iff.mpr hqs))
        (Finset.insert_nonempty p {q})
    refine mem_iUnion₂.mpr ⟨q, ⟨hqp', hedge⟩,
      (K.barycentricDualBlock {p, q}).convexHull_subset_space ⟨hf.1, ?_⟩ hxf⟩
    intro y hy
    obtain ⟨t, ht, hty⟩ := Finset.mem_image.mp (hfa ▸ hy)
    exact ⟨t, hfaces t ht,
      Finset.insert_subset (hpa t ht) (Finset.singleton_subset_iff.mpr (hst t ht hqs)), hty⟩
  · intro x hx
    obtain ⟨q, hq, hx⟩ := mem_iUnion₂.mp hx
    have hqK : q ∈ K.vertices :=
      K.face_subset_vertices hq.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
    exact (K.dualEdge_space_subset_vertex_links hp hqK (Ne.symm hq.1) hx).1

end Geometry.SimplicialComplex
