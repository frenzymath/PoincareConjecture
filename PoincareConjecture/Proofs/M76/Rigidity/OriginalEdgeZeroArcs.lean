import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskEdgeCofaces
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDualRegion
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricBoundaryFacetInterval

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in
private theorem rim_edge_dualBlock_space
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 3).faces)
    (hscard : s.card = 2) :
    let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
    ((T.marked 3).barycentricDualBlock s).space = {s.centroid ℝ id} := by
  classical
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  change ((T.marked 3).barycentricDualBlock s).space = {s.centroid ℝ id}
  apply Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hverts : (a : Set (T.index → ℝ × V3)) ⊆ {s.centroid ℝ id} := by
      intro y hy
      obtain ⟨t, ht, hst, hty⟩ := ha.2 y hy
      have hts : t = s := (Finset.eq_of_subset_of_card_le hst (by
        have hbound := T.rim_face_card_le ht
        omega)).symm
      exact hty.symm.trans (congrArg (fun v => v.centroid ℝ id) hts)
    simpa only [convexHull_singleton] using convexHull_mono hverts hxa
  · rintro x rfl
    exact ((T.marked 3).barycentricDualBlock s).vertices_subset_space
      ((T.marked 3).faceCentroid_mem_barycentricDualBlock_vertices hs)

theorem exists_edge_zero_arc
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 2) :
    ∃ a z : (T.index → ℝ × V3), a ≠ z ∧
      IsFinitePLBallPair ℝ (T.dualRegion s ∩ (T.marked 2).space) {a, z} ∧
      T.dualRegionRim s ∩ (T.marked 2).space = {a, z} := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  let L := (T.marked 2).barycentricDualBlock s
  let B := (T.marked 3).barycentricDualBlock s
  let cs := s.centroid ℝ id
  have hzero : T.dualRegion s ∩ (T.marked 2).space = L.space :=
    T.dualRegion_inter_disk s
  have hrim : T.dualRegionRim s ∩ (T.marked 2).space =
      (L.link cs).space ∪ B.space := T.dualRegionRim_inter_disk hs
  have hbound : ∀ v ∈ (T.marked 2).faces, v.card ≤ 2 + 1 :=
    fun _ hv => T.disk_face_card_le hv
  by_cases hsQ : s ∈ (T.marked 3).faces
  · obtain ⟨t, ht, hst, htc, hunique⟩ := T.exists_rim_edge_triangle_coface hs hscard hsQ
    have hpair := (T.marked 2).barycentricDualBlock_of_single_coface
      hbound hs ht hscard htc hst hunique
    have hB : B.space = {cs} := rim_edge_dualBlock_space T hsQ hscard
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

end PoincareConjecture.M76.OriginalProperDiskTriangulation
