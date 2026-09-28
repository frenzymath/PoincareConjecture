import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.SurfaceStars
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.DualPointCoface
import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSaturation

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (T : CoorientedSurfaceStars E)

open Classical in

noncomputable def dualRegion (s : Finset E) : Set E :=
  let : Fintype T.ambient.faces := T.finite.fintype
  (T.ambient.barycentricDualBlock s).space ∩ (T.marked 0).space

open Classical in

noncomputable def dualRegionRim (s : Finset E) : Set E :=
  let : Fintype T.ambient.faces := T.finite.fintype
  (((T.ambient.barycentricDualBlock s).link (s.centroid ℝ id)).space ∩
    (T.marked 0).space) ∪ ((T.ambient.barycentricDualBlock s).space ∩ (T.marked 1).space)

noncomputable def surfaceBase (s : Finset E) : Set E :=
  T.dualRegion s ∩ (T.marked 2).space

open Classical in

theorem dualRegion_inter_surface (s : Finset E) :
    let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
    T.dualRegion s ∩ (T.marked 2).space = ((T.marked 2).barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  change ((T.ambient.barycentricDualBlock s).space ∩ (T.marked 0).space) ∩
    (T.marked 2).space = _
  rw [inter_assoc, inter_eq_right.mpr T.surface_subset_region]
  exact T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 2) (T.marked_le 2) s

open Classical in

theorem dualRegion_inter_boundary (s : Finset E) :
    let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
    T.dualRegion s ∩ (T.marked 1).space = ((T.marked 1).barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  change ((T.ambient.barycentricDualBlock s).space ∩ (T.marked 0).space) ∩
    (T.marked 1).space = _
  rw [inter_assoc, inter_eq_right.mpr T.boundary_subset_region]
  exact T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 1) (T.marked_le 1) s

open Classical in

theorem surface_dual_inter_boundary (s : Finset E) :
    let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
    let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
    ((T.marked 2).barycentricDualBlock s).space ∩ (T.marked 1).space =
      ((T.marked 3).barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  change ((T.marked 2).barycentricDualBlock s).space ∩ (T.marked 1).space = _
  rw [← T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 2) (T.marked_le 2) s, inter_assoc, T.surface_boundary_inter]
  exact T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 3) (T.marked_le 3) s

open Classical in

theorem dualRegionRim_inter_surface {s : Finset E} (hs : s ∈ (T.marked 2).faces) :
    let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
    let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
    T.dualRegionRim s ∩ (T.marked 2).space =
      (((T.marked 2).barycentricDualBlock s).link (s.centroid ℝ id)).space ∪
        ((T.marked 3).barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  let N := T.ambient.barycentricDualBlock s
  let L := (T.marked 2).barycentricDualBlock s
  let c := s.centroid ℝ id
  have hND : N.space ∩ (T.marked 2).space = L.space :=
    T.ambient.barycentricDualBlock_space_inter_subcomplex (T.marked 2) (T.marked_le 2) s
  have hLN : L ≤ N :=
    T.ambient.barycentricDualBlock_mono_of_subcomplex (T.marked 2) (T.marked_le 2) s
  have hlink : (L.link c).space = L.space ∩ (N.link c).space :=
    link_space_eq_inter_of_closedStar_eq N L hLN c
      ((T.marked 2).barycentricDualBlock_closedStar_faceCentroid hs)
  have hNL : (N.link c).space ⊆ N.space := space_subset_of_le (fun _ ht => ht.1)
  have hrim : T.dualRegionRim s ∩ (T.marked 2).space =
      (L.link c).space ∪ (L.space ∩ (T.marked 1).space) := by
    change (((N.link c).space ∩ (T.marked 0).space) ∪
      (N.space ∩ (T.marked 1).space)) ∩ (T.marked 2).space = _
    ext x
    constructor
    · rintro ⟨hx | hx, hxS⟩
      · exact Or.inl (hlink.symm.subset ⟨hND.subset ⟨hNL hx.1, hxS⟩, hx.1⟩)
      · exact Or.inr ⟨hND.subset ⟨hx.1, hxS⟩, hx.2⟩
    · rintro (hx | hx)
      · obtain ⟨hxD, hxN⟩ := hlink.subset hx
        have h := hND.symm.subset hxD
        exact ⟨Or.inl ⟨hxN, T.surface_subset_region h.2⟩, h.2⟩
      · have h := hND.symm.subset hx.1
        exact ⟨Or.inr ⟨h.1, hx.2⟩, h.2⟩
  exact hrim.trans (congrArg (fun B => (L.link c).space ∪ B)
    (T.surface_dual_inter_boundary s))

open Classical in

theorem dualBlock_subset_star (p : (T.marked 2).vertices)
    {s : Finset E} (hps : (p : E) ∈ s) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ⊆ (T.ambient.closedStar p).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  change (T.ambient.barycentricDualBlock s).space ⊆ (T.ambient.closedStar p).space
  intro x hx
  obtain ⟨t, ht, hst, hxt⟩ := T.ambient.exists_coface_of_mem_dualBlock hx
  exact (T.ambient.closedStar p).convexHull_subset_space
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using ht⟩ hxt

theorem dualRegion_subset_star (p : (T.marked 2).vertices)
    {s : Finset E} (hps : (p : E) ∈ s) :
    T.dualRegion s ⊆ (T.ambient.closedStar p).space :=
  fun _ hx => T.dualBlock_subset_star p hps hx.1

theorem dualRegion_antitone {s t : Finset E} (hst : s ⊆ t) :
    T.dualRegion t ⊆ T.dualRegion s := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  intro x hx
  exact ⟨space_subset_of_le (T.ambient.barycentricDualBlock_antitone hst) hx.1, hx.2⟩

theorem dualRegion_inter (s t : Finset E) :
    T.dualRegion s ∩ T.dualRegion t = T.dualRegion (s ∪ t) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have h := T.ambient.barycentricDualBlock_space_inter s t
  ext x
  exact ⟨fun hx => ⟨h.subset ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩,
    fun hx => ⟨⟨(h.symm.subset hx.1).1, hx.2⟩, (h.symm.subset hx.1).2, hx.2⟩⟩

theorem surfaceBase_inter (s t : Finset E) :
    T.surfaceBase s ∩ T.surfaceBase t = T.surfaceBase (s ∪ t) := by
  change (T.dualRegion s ∩ (T.marked 2).space) ∩
    (T.dualRegion t ∩ (T.marked 2).space) = _
  rw [show T.surfaceBase (s ∪ t) =
    (T.dualRegion s ∩ T.dualRegion t) ∩ (T.marked 2).space by
      rw [T.dualRegion_inter]; rfl]
  ext x
  simp only [mem_inter_iff]
  tauto

theorem dualRegion_eq_empty_of_not_surface_face {s : Finset E}
    (hne : s.Nonempty) (hverts : (s : Set E) ⊆ (T.marked 2).vertices)
    (hs : s ∉ (T.marked 2).faces) : T.dualRegion s = ∅ := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have hsA : s ∉ T.ambient.faces := fun h => hs (T.marked_full 2 s h (fun _ hv => hverts hv))
  change (T.ambient.barycentricDualBlock s).space ∩ (T.marked 0).space = ∅
  rw [T.ambient.barycentricDualBlock_space_eq_empty_of_not_face hne hsA, empty_inter]

theorem dualRegionRim_subset (s : Finset E) : T.dualRegionRim s ⊆ T.dualRegion s := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have hlink : (T.ambient.barycentricDualBlock s).link (s.centroid ℝ id) ≤
      T.ambient.barycentricDualBlock s := fun _ ht => ht.1
  rintro x (hx | hx)
  · exact ⟨space_subset_of_le hlink hx.1, hx.2⟩
  · exact ⟨hx.1, T.boundary_subset_region hx.2⟩

theorem dualRegion_subset_rim_of_ssubset {s t : Finset E}
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
  exact Or.inl ⟨space_subset_of_le hML hx.1, hx.2⟩

end Geometry.SimplicialComplex.CoorientedSurfaceStars
