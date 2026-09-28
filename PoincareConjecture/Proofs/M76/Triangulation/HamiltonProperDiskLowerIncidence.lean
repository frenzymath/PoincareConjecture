import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskLowerProducts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskTriangleBoundary
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualContact










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}



theorem HamiltonProperDiskTriangulation.diskDualBase_eq_dual
    (T : HamiltonProperDiskTriangulation R D b) (s : Finset E) :
    let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
    T.diskDualBase s = (T.disk.barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  have hND : (T.ambient.barycentricDualBlock s).space ∩ D =
      (T.disk.barycentricDualBlock s).space := by
    simpa only [T.disk_space] using
      T.ambient.barycentricDualBlock_space_inter_subcomplex T.disk T.disk_le s
  ext x
  constructor
  · exact fun hx => hND.subset ⟨hx.1.1, hx.2⟩
  · intro hx
    obtain ⟨hxN, hxD⟩ := hND.symm.subset hx
    exact ⟨⟨hxN, T.disk_subset_region hxD⟩, hxD⟩



theorem HamiltonProperDiskTriangulation.dualRegion_subset_rim_of_ssubset
    (T : HamiltonProperDiskTriangulation R D b) {s t : Finset E}
    (hs : s ∈ T.disk.faces) (_ht : t ∈ T.disk.faces) (hst : s ⊂ t) :
    T.dualRegion t ⊆ T.dualRegionRim s := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.ambient.barycentricDualBlock s
  let M := T.ambient.barycentricDualBlock t
  have hMN : M ≤ N := T.ambient.barycentricDualBlock_antitone hst.subset
  have hML : M ≤ N.link (s.centroid ℝ id) := by
    intro a ha
    have haN := hMN ha
    have hastar : a ∈ (N.closedStar (s.centroid ℝ id)).faces :=
      (T.ambient.barycentricDualBlock_closedStar_faceCentroid (T.disk_le hs)).symm ▸ haN
    refine ⟨haN, ?_, hastar.2⟩
    intro hcs
    obtain ⟨u, hu, htu, he⟩ := ha.2 _ hcs
    have heq : (⟨u, hu⟩ : T.ambient.faces) = ⟨s, T.disk_le hs⟩ :=
      T.ambient.faceCentroid_injective he
    have hus : u = s := congrArg Subtype.val heq
    exact hst.not_subset (hus ▸ htu)
  intro x hx
  exact Or.inl ⟨SimplicialComplex.space_subset_of_le hML hx.1, hx.2⟩



theorem HamiltonProperDiskTriangulation.dualRegion_inter
    (T : HamiltonProperDiskTriangulation R D b) (s t : Finset E) :
    T.dualRegion s ∩ T.dualRegion t = T.dualRegion (s ∪ t) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have h := T.ambient.barycentricDualBlock_space_inter s t
  ext x
  constructor
  · exact fun hx => ⟨h.subset ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  · intro hx
    have hxt := h.symm.subset hx.1
    exact ⟨⟨hxt.1, hx.2⟩, hxt.2, hx.2⟩




theorem HamiltonProperDiskTriangulation.dualRegion_eq_empty_of_not_disk_face
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E}
    (hne : s.Nonempty) (hverts : (s : Set E) ⊆ T.disk.vertices) (hs : s ∉ T.disk.faces) :
    T.dualRegion s = ∅ := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have hsA : s ∉ T.ambient.faces := fun h => hs (T.disk_full s h (fun v hv => hverts hv))
  have he := T.ambient.barycentricDualBlock_space_eq_empty_of_not_face hne hsA
  change (T.ambient.barycentricDualBlock s).space ∩ R = ∅
  rw [he, empty_inter]

variable [FiniteDimensional ℝ E]



theorem HamiltonProperDiskTriangulation.triangle_base_eq_singleton
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E}
    (hs : s ∈ T.disk.faces) (hcard : s.card = 3) :
    T.diskDualBase s = {s.centroid ℝ id} := by
  classical
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  rw [T.diskDualBase_eq_dual]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hverts : (a : Set E) ⊆ {s.centroid ℝ id} := by
      intro y hy
      obtain ⟨u, hu, hsu, huy⟩ := ha.2 y hy
      have hus : u = s := (Finset.eq_of_subset_of_card_le hsu
        (by rw [hcard]; exact T.disk_face_card_le hu)).symm
      exact huy.symm.trans (congrArg (fun v : Finset E => v.centroid ℝ id) hus)
    simpa only [convexHull_singleton] using convexHull_mono hverts hxa
  · rintro x rfl
    exact (T.disk.barycentricDualBlock s).vertices_subset_space
      (T.disk.faceCentroid_mem_barycentricDualBlock_vertices hs)




theorem HamiltonProperDiskTriangulation.boundary_edge_base_contact
    (T : HamiltonProperDiskTriangulation R D b)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 2)
    (hsF : s ∈ T.boundary.faces) :
    T.diskDualBase s ∩ frontier R = {s.centroid ℝ id} := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  let : Fintype T.boundary.faces := (T.finite.subset T.boundary_le).fintype
  let N := T.ambient.barycentricDualBlock s
  let L := T.disk.barycentricDualBlock s
  let F := T.boundary.barycentricDualBlock s
  have hcommon : ∀ u ∈ T.disk.faces, u ∈ T.boundary.faces → s ⊆ u → u = s := by
    intro u hu huf hsu
    by_contra hus
    have hlt := Finset.card_lt_card (hsu.ssubset_of_ne (Ne.symm hus))
    have hbound := T.disk_face_card_le hu
    exact T.disk_triangle_not_boundary hproper hu (by omega) huf
  have hcontact : L.space ∩ F.space = {s.centroid ℝ id} :=
    T.ambient.dualBlocks_inter_eq_centroid_of_no_common_coface
      T.disk T.boundary T.disk_le T.boundary_le hs hsF hcommon
  have hLN : L.space ⊆ N.space := SimplicialComplex.space_subset_of_le
    (T.ambient.barycentricDualBlock_mono_of_subcomplex T.disk T.disk_le s)
  have hNF : N.space ∩ frontier R = F.space := by
    simpa only [T.boundary_space] using
      T.ambient.barycentricDualBlock_space_inter_subcomplex T.boundary T.boundary_le s
  rw [T.diskDualBase_eq_dual]
  change L.space ∩ frontier R = _
  calc
    L.space ∩ frontier R = L.space ∩ (N.space ∩ frontier R) := by
      rw [← inter_assoc, inter_eq_left.mpr hLN]
    _ = {s.centroid ℝ id} := by rw [hNF, hcontact]

end PoincareConjecture.M76.HamiltonIndexOne
