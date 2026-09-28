import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.SurfaceIncidence
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.Duals
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricBoundaryFacetInterval
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MaximalFaceDual



set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

theorem exists_rim_edge_triangle_coface {s : Finset E}
    (_hs : s ∈ (T.marked 2).faces) (hscard : s.card = 2)
    (hsQ : s ∈ (T.marked 3).faces) :
    ∃ t ∈ (T.marked 2).faces, s ⊆ t ∧ t.card = 3 ∧
      ∀ v ∈ (T.marked 2).faces, s ⊆ v → v.card = 3 → v = t := by
  have hcount := T.surface_edge_faceLink_ncard_eq_one hsQ hscard
  rw [(T.marked 2).ncard_faceLink_vertices_eq_cofaces, hscard] at hcount
  obtain ⟨t, heq⟩ := ncard_eq_one.mp hcount
  have ht : t ∈ {u : Finset E | u ∈ (T.marked 2).faces ∧ u.card = 3 ∧ s ⊆ u} :=
    heq.symm.subset rfl
  exact ⟨t, ht.1, ht.2.2, ht.2.1, fun v hv hsv hvc ↦ heq.subset ⟨hv, hvc, hsv⟩⟩

theorem exists_interior_edge_triangle_cofaces {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 2)
    (hsQ : s ∉ (T.marked 3).faces) :
    ∃ t ∈ (T.marked 2).faces, ∃ v ∈ (T.marked 2).faces,
      s ⊆ t ∧ s ⊆ v ∧ t.card = 3 ∧ v.card = 3 ∧ t ≠ v ∧
      ∀ u ∈ (T.marked 2).faces, s ⊆ u → u.card = 3 → u = t ∨ u = v := by
  have hcount := T.surface_edge_faceLink_ncard_eq_two hs hscard hsQ
  rw [(T.marked 2).ncard_faceLink_vertices_eq_cofaces, hscard] at hcount
  obtain ⟨t, v, htv, heq⟩ := ncard_eq_two.mp hcount
  have ht : t ∈ {u : Finset E | u ∈ (T.marked 2).faces ∧ u.card = 3 ∧ s ⊆ u} :=
    heq.symm.subset (Or.inl rfl)
  have hv : v ∈ {u : Finset E | u ∈ (T.marked 2).faces ∧ u.card = 3 ∧ s ⊆ u} :=
    heq.symm.subset (Or.inr rfl)
  exact ⟨t, ht.1, v, hv.1, ht.2.2, hv.2.2, ht.2.1, hv.2.1, htv,
    fun u hu hsu huc ↦ heq.subset ⟨hu, huc, hsu⟩⟩

open Classical in
theorem rim_edge_dualBlock_space {s : Finset E} (hs : s ∈ (T.marked 3).faces)
    (hscard : s.card = 2) :
    let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
    ((T.marked 3).barycentricDualBlock s).space = {s.centroid ℝ id} := by
  classical
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  apply (T.marked 3).barycentricDualBlock_space_eq_singleton_of_maximal hs
  intro t ht hst
  exact (Finset.eq_of_subset_of_card_le hst (by
    rw [hscard]
    exact T.rim_face_card_le_two ht)).symm



theorem exists_edge_zero_arc {s : Finset E} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 2) :
    ∃ a z : E, a ≠ z ∧
      IsFinitePLBallPair ℝ (T.dualRegion s ∩ (T.marked 2).space) {a, z} ∧
      T.dualRegionRim s ∩ (T.marked 2).space = {a, z} := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  let L := (T.marked 2).barycentricDualBlock s
  let B := (T.marked 3).barycentricDualBlock s
  let cs := s.centroid ℝ id
  have hzero : T.dualRegion s ∩ (T.marked 2).space = L.space := T.dualRegion_inter_surface s
  have hrim : T.dualRegionRim s ∩ (T.marked 2).space =
      (L.link cs).space ∪ B.space := T.dualRegionRim_inter_surface hs
  have hbound : ∀ v ∈ (T.marked 2).faces, v.card ≤ 2 + 1 :=
    fun _ hv ↦ T.surface_face_card_le_three hv
  by_cases hsQ : s ∈ (T.marked 3).faces
  · obtain ⟨t, ht, hst, htc, hunique⟩ := T.exists_rim_edge_triangle_coface hs hscard hsQ
    have hpair := (T.marked 2).barycentricDualBlock_of_single_coface
      hbound hs ht hscard htc hst hunique
    have hB : B.space = {cs} := T.rim_edge_dualBlock_space hsQ hscard
    have hne : cs ≠ t.centroid ℝ id := by
      intro he
      have heq : (⟨s, hs⟩ : (T.marked 2).faces) = ⟨t, ht⟩ :=
        (T.marked 2).faceCentroid_injective he
      have hst' : s = t := congrArg Subtype.val heq
      rw [hst', htc] at hscard
      omega
    refine ⟨cs, t.centroid ℝ id, hne, ?_, ?_⟩
    · rw [hzero]
      exact hpair.2.1
    · rw [hrim, hpair.2.2, hB]
      ext x
      simp only [mem_union, mem_insert_iff, mem_singleton_iff]
      tauto
  · obtain ⟨t, ht, v, hv, hst, hsv, htc, hvc, htv, hcofaces⟩ :=
      T.exists_interior_edge_triangle_cofaces hs hscard hsQ
    have hpair := (T.marked 2).isFinitePLBallPair_barycentricDualBlock_of_paired_facet
      hbound hs ht hv hscard htc hvc hst hsv htv hcofaces
    have hlink := (T.marked 2).barycentricDualBlock_link_space_of_paired_facet
      hbound hs ht hv hscard htc hvc hst hsv hcofaces
    have hB : B.space = ∅ :=
      (T.marked 3).barycentricDualBlock_space_eq_empty_of_not_face
        ((T.marked 2).nonempty_of_mem_faces hs) hsQ
    have hne : t.centroid ℝ id ≠ v.centroid ℝ id := by
      intro he
      have heq : (⟨t, ht⟩ : (T.marked 2).faces) = ⟨v, hv⟩ :=
        (T.marked 2).faceCentroid_injective he
      exact htv (congrArg Subtype.val heq)
    refine ⟨t.centroid ℝ id, v.centroid ℝ id, hne, ?_, ?_⟩
    · rw [hzero]
      exact hpair.1
    · rw [hrim, hlink, hB, union_empty]

theorem boundary_edge_base_contact {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 2) (hsB : s ∈ (T.marked 1).faces) :
    (T.dualRegion s ∩ (T.marked 2).space) ∩ (T.marked 1).space =
      {s.centroid ℝ id} := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  rw [T.dualRegion_inter_surface, T.surface_dual_inter_boundary]
  exact T.rim_edge_dualBlock_space ((T.surface_face_mem_boundary_iff hs).mp hsB) hcard

end Geometry.SimplicialComplex.CoorientedSurfaceStars
