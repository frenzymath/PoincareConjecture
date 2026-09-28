import PoincareConjecture.Proofs.M76.Rigidity.OriginalDualRegion
import PoincareConjecture.Proofs.M76.Rigidity.OriginalRegionClosed
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MaximalFaceDual









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)




theorem triangle_base_eq_singleton {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 3) :
    T.dualRegion s ∩ (T.marked 2).space = {s.centroid ℝ id} := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  rw [T.dualRegion_inter_disk]
  apply (T.marked 2).barycentricDualBlock_space_eq_singleton_of_maximal hs
  intro t ht hst
  exact (Finset.eq_of_subset_of_card_le hst (by
    rw [hcard]
    exact T.disk_face_card_le ht)).symm




theorem disk_triangle_not_boundary {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 3) :
    s ∉ (T.marked 1).faces := by
  intro hsB
  have hbound := T.rim_face_card_le ((T.disk_face_mem_boundary_iff hs).mp hsB)
  omega



theorem boundary_edge_base_contact {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 2)
    (hsB : s ∈ (T.marked 1).faces) :
    (T.dualRegion s ∩ (T.marked 2).space) ∩ (T.marked 1).space =
      {s.centroid ℝ id} := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  rw [T.dualRegion_inter_disk, T.disk_dual_inter_boundary]
  apply (T.marked 3).barycentricDualBlock_space_eq_singleton_of_maximal
    ((T.disk_face_mem_boundary_iff hs).mp hsB)
  intro t ht hst
  exact (Finset.eq_of_subset_of_card_le hst (by
    rw [hcard]
    exact T.rim_face_card_le ht)).symm

open Classical in


theorem dualRegion_subset_rim_of_ssubset {s t : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hst : s ⊂ t) :
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
      (T.ambient.barycentricDualBlock_closedStar_faceCentroid (T.marked_le 2 hs)).symm ▸ haN
    refine ⟨haN, ?_, hastar.2⟩
    intro hcs
    obtain ⟨u, hu, htu, he⟩ := ha.2 _ hcs
    have heq : (⟨u, hu⟩ : T.ambient.faces) = ⟨s, T.marked_le 2 hs⟩ :=
      T.ambient.faceCentroid_injective he
    have hus : u = s := congrArg Subtype.val heq
    exact hst.not_subset (hus ▸ htu)
  intro x hx
  exact Or.inl ⟨SimplicialComplex.space_subset_of_le hML hx.1, hx.2⟩

open Classical in


theorem dualRegion_inter (s t : Finset (T.index → ℝ × V3)) :
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



theorem dualRegion_eq_empty_of_not_disk_face {s : Finset (T.index → ℝ × V3)}
    (hne : s.Nonempty) (hverts : (s : Set (T.index → ℝ × V3)) ⊆ (T.marked 2).vertices)
    (hs : s ∉ (T.marked 2).faces) : T.dualRegion s = ∅ := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have hsA : s ∉ T.ambient.faces := fun h => hs (T.marked_full 2 s h (fun _ hv => hverts hv))
  have he := T.ambient.barycentricDualBlock_space_eq_empty_of_not_face hne hsA
  change (T.ambient.barycentricDualBlock s).space ∩ (T.marked 0).space = ∅
  rw [he, empty_inter]

open Classical in


theorem dualRegion_inter_boundary [T2Space X] (s : Finset (T.index → ℝ × V3)) :
    let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
    T.dualRegion s ∩ (T.marked 1).space = ((T.marked 1).barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  change ((T.ambient.barycentricDualBlock s).space ∩ (T.marked 0).space) ∩
    (T.marked 1).space = _
  rw [inter_assoc, inter_eq_right.mpr T.boundary_space_subset_region]
  exact T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 1) (T.marked_le 1) s

end PoincareConjecture.M76.OriginalProperDiskTriangulation
