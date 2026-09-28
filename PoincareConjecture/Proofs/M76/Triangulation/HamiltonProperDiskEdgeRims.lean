import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskDualSigns
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskDualIncidence
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskInteriorEdges
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskTriangleBoundary
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricBoundaryFacetInterval
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualContact










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}



noncomputable def HamiltonProperDiskTriangulation.dualRegionRim
    (T : HamiltonProperDiskTriangulation R D b) (s : Finset E) : Set E :=
  let : Fintype T.ambient.faces := T.finite.fintype
  (((T.ambient.barycentricDualBlock s).link (s.centroid ℝ id)).space ∩ R) ∪
    ((T.ambient.barycentricDualBlock s).space ∩ frontier R)

private theorem dualRegion_inter_disk
    (T : HamiltonProperDiskTriangulation R D b) (s : Finset E) :
    let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
    T.dualRegion s ∩ D = (T.disk.barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  have hND : (T.ambient.barycentricDualBlock s).space ∩ D =
      (T.disk.barycentricDualBlock s).space := by
    simpa only [T.disk_space] using
      T.ambient.barycentricDualBlock_space_inter_subcomplex T.disk T.disk_le s
  ext x
  constructor
  · intro hx
    exact hND.subset ⟨hx.1.1, hx.2⟩
  · intro hx
    obtain ⟨hxN, hxD⟩ := hND.symm.subset hx
    exact ⟨⟨hxN, T.disk_subset_region hxD⟩, hxD⟩

private theorem dualRegionRim_inter_disk
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E}
    (hs : s ∈ T.disk.faces) :
    let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
    T.dualRegionRim s ∩ D =
      ((T.disk.barycentricDualBlock s).link (s.centroid ℝ id)).space ∪
        ((T.disk.barycentricDualBlock s).space ∩ frontier R) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  let N := T.ambient.barycentricDualBlock s
  let L := T.disk.barycentricDualBlock s
  let cs := s.centroid ℝ id
  have hND : N.space ∩ D = L.space := by
    simpa only [T.disk_space] using
      T.ambient.barycentricDualBlock_space_inter_subcomplex T.disk T.disk_le s
  have hL : L ≤ N := T.ambient.barycentricDualBlock_mono_of_subcomplex T.disk T.disk_le s
  have hlink : (L.link cs).space = L.space ∩ (N.link cs).space :=
    SimplicialComplex.link_space_eq_inter_of_closedStar_eq N L hL cs
      (T.disk.barycentricDualBlock_closedStar_faceCentroid hs)
  have hNL : (N.link cs).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (fun _ hf => hf.1)
  change (((N.link cs).space ∩ R) ∪ (N.space ∩ frontier R)) ∩ D =
    (L.link cs).space ∪ (L.space ∩ frontier R)
  ext x
  constructor
  · intro hx
    rcases hx.1 with hxL | hxF
    · exact Or.inl (hlink.symm.subset ⟨hND.subset ⟨hNL hxL.1, hx.2⟩, hxL.1⟩)
    · exact Or.inr ⟨hND.subset ⟨hxF.1, hx.2⟩, hxF.2⟩
  · intro hx
    rcases hx with hxL | hxF
    · obtain ⟨hxD, hxN⟩ := hlink.subset hxL
      have h := hND.symm.subset hxD
      exact ⟨Or.inl ⟨hxN, T.disk_subset_region h.2⟩, h.2⟩
    · have h := hND.symm.subset hxF.1
      exact ⟨Or.inr ⟨h.1, hxF.2⟩, h.2⟩

variable [FiniteDimensional ℝ E]





theorem HamiltonProperDiskTriangulation.exists_edge_zero_arc
    (T : HamiltonProperDiskTriangulation R D b)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 2) :
    ∃ a z : E, a ≠ z ∧ IsFinitePLBallPair ℝ (T.dualRegion s ∩ D) {a, z} ∧
      T.dualRegionRim s ∩ D = {a, z} := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  let : Fintype T.boundary.faces := (T.finite.subset T.boundary_le).fintype
  let N := T.ambient.barycentricDualBlock s
  let L := T.disk.barycentricDualBlock s
  let B := T.boundary.barycentricDualBlock s
  let cs := s.centroid ℝ id
  have hzero : T.dualRegion s ∩ D = L.space := dualRegion_inter_disk T s
  have hrim : T.dualRegionRim s ∩ D =
      (L.link cs).space ∪ (L.space ∩ frontier R) := dualRegionRim_inter_disk T hs
  have hLN : L.space ⊆ N.space := SimplicialComplex.space_subset_of_le
    (T.ambient.barycentricDualBlock_mono_of_subcomplex T.disk T.disk_le s)
  have hbound : ∀ v ∈ T.disk.faces, v.card ≤ 2 + 1 := fun _ hv => T.disk_face_card_le hv
  by_cases hsF : s ∈ T.boundary.faces
  · have hboundary : convexHull ℝ (s : Set E) ⊆ frontier R :=
      (T.boundary.convexHull_subset_space hsF).trans T.boundary_space.subset
    obtain ⟨t, ht, hst, htc, hunique⟩ :=
      T.exists_boundary_triangle_coface hproper hs hcard hboundary
    have hpair := T.disk.barycentricDualBlock_of_single_coface
      hbound hs ht hcard htc hst hunique
    have hcommon : ∀ v ∈ T.disk.faces, v ∈ T.boundary.faces → s ⊆ v → v = s := by
      intro v hvD hvF hsv
      by_contra hvne
      have hlt := Finset.card_lt_card (hsv.ssubset_of_ne (Ne.symm hvne))
      have hle := T.disk_face_card_le hvD
      have hvc : v.card = 3 := by omega
      exact T.disk_triangle_not_boundary hproper hvD hvc hvF
    have hcontact : L.space ∩ B.space = {cs} :=
      T.ambient.dualBlocks_inter_eq_centroid_of_no_common_coface
        T.disk T.boundary T.disk_le T.boundary_le hs hsF hcommon
    have hNF : N.space ∩ frontier R = B.space := by
      simpa only [T.boundary_space] using
        T.ambient.barycentricDualBlock_space_inter_subcomplex T.boundary T.boundary_le s
    have hfront : L.space ∩ frontier R = {cs} := by
      calc
        L.space ∩ frontier R = L.space ∩ (N.space ∩ frontier R) := by
          rw [← inter_assoc, inter_eq_left.mpr hLN]
        _ = {cs} := by rw [hNF, hcontact]
    have hne : cs ≠ t.centroid ℝ id := by
      intro he
      have heq : (⟨s, hs⟩ : T.disk.faces) = ⟨t, ht⟩ := T.disk.faceCentroid_injective he
      have hst' : s = t := congrArg Subtype.val heq
      rw [hst', htc] at hcard
      omega
    refine ⟨cs, t.centroid ℝ id, hne, ?_, ?_⟩
    · rw [hzero]
      exact hpair.2.1
    · rw [hrim, hpair.2.2, hfront]
      ext x
      simp only [mem_union, mem_insert_iff, mem_singleton_iff]
      tauto
  · have hNint : N.space ⊆ interior R := T.dualBlock_subset_interior hs hsF
    have hcs : cs ∈ N.space := N.vertices_subset_space
      (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices (T.disk_le hs))
    have hmeet : (convexHull ℝ (s : Set E) ∩ interior R).Nonempty :=
      ⟨cs, s.centroid_mem_convexHull (T.disk.nonempty_of_mem_faces hs), hNint hcs⟩
    obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hcofaces⟩ :=
      T.exists_interior_triangle_cofaces hproper hs hcard hmeet
    have hpair := T.disk.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
      hbound hs ht hu hcard htc huc hst hsu htu hcofaces
    have hlink := T.disk.barycentricDualBlock_link_space_of_paired_facet
      hbound hs ht hu hcard htc huc hst hsu hcofaces
    have hfront : L.space ∩ frontier R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.2.2 (hNint (hLN hx.1))
    have hne : t.centroid ℝ id ≠ u.centroid ℝ id := by
      intro he
      have heq : (⟨t, ht⟩ : T.disk.faces) = ⟨u, hu⟩ := T.disk.faceCentroid_injective he
      exact htu (congrArg Subtype.val heq)
    refine ⟨t.centroid ℝ id, u.centroid ℝ id, hne, ?_, ?_⟩
    · rw [hzero]
      exact hpair.1
    · rw [hrim, hlink, hfront, union_empty]

end PoincareConjecture.M76.HamiltonIndexOne
