import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalDiskParameter
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricDualSubcomplex

/-!
# Entire original region duals and their complete marked rim contact

Both region and old-boundary restrictions use the same four retained
marks. Intersecting with the whole disk gives its own actual dual and
the exact union of its centroid link and rim dual.
See Hudson1969, pp.8--9,58--63 and rigidity022, section3.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in
/-- The literal part of an ambient dual block in the complete original
region mark. See rigidity022, section3. -/
noncomputable def dualRegion (s : Finset (T.index → ℝ × V3)) :
    Set (T.index → ℝ × V3) :=
  let : Fintype T.ambient.faces := T.finite.fintype
  (T.ambient.barycentricDualBlock s).space ∩ (T.marked 0).space

open Classical in
/-- The complete rim includes both the ambient centroid link in the
region and the entire original boundary contact. See rigidity022. -/
noncomputable def dualRegionRim (s : Finset (T.index → ℝ × V3)) :
    Set (T.index → ℝ × V3) :=
  let : Fintype T.ambient.faces := T.finite.fintype
  (((T.ambient.barycentricDualBlock s).link (s.centroid ℝ id)).space ∩
    (T.marked 0).space) ∪ ((T.ambient.barycentricDualBlock s).space ∩ (T.marked 1).space)

open Classical in
/-- The whole disk contact of the literal region dual is precisely
the dual formed in the same disk mark. See rigidity022, section3. -/
theorem dualRegion_inter_disk (s : Finset (T.index → ℝ × V3)) :
    let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
    T.dualRegion s ∩ (T.marked 2).space = ((T.marked 2).barycentricDualBlock s).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  have hND := T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 2) (T.marked_le 2) s
  change ((T.ambient.barycentricDualBlock s).space ∩ (T.marked 0).space) ∩
    (T.marked 2).space = ((T.marked 2).barycentricDualBlock s).space
  ext x
  constructor
  · exact fun hx => hND.subset ⟨hx.1.1, hx.2⟩
  · intro hx
    obtain ⟨hxN, hxD⟩ := hND.symm.subset hx
    exact ⟨⟨hxN, T.disk_space_subset_region hxD⟩, hxD⟩

open Classical in
/-- The whole original-boundary contact of a disk dual is exactly
the dual in the unchanged complete rim mark. See rigidity022, section3. -/
theorem disk_dual_inter_boundary (s : Finset (T.index → ℝ × V3)) :
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
    (T.marked 2) (T.marked_le 2) s, inter_assoc, T.disk_boundary_inter]
  exact T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 3) (T.marked_le 3) s

open Classical in
/-- Every point of the complete region-dual rim on the disk belongs
to its literal centroid link or to the whole rim dual, and conversely.
No disk-boundary conclusion is assumed. See rigidity022, section3. -/
theorem dualRegionRim_inter_disk {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) :
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
  let cs := s.centroid ℝ id
  have hND : N.space ∩ (T.marked 2).space = L.space :=
    T.ambient.barycentricDualBlock_space_inter_subcomplex (T.marked 2) (T.marked_le 2) s
  have hLN : L ≤ N :=
    T.ambient.barycentricDualBlock_mono_of_subcomplex (T.marked 2) (T.marked_le 2) s
  have hlink : (L.link cs).space = L.space ∩ (N.link cs).space :=
    SimplicialComplex.link_space_eq_inter_of_closedStar_eq N L hLN cs
      ((T.marked 2).barycentricDualBlock_closedStar_faceCentroid hs)
  have hNL : (N.link cs).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (show N.link cs ≤ N from fun _ ht => ht.1)
  have hrim : T.dualRegionRim s ∩ (T.marked 2).space =
      (L.link cs).space ∪ (L.space ∩ (T.marked 1).space) := by
    change (((N.link cs).space ∩ (T.marked 0).space) ∪
        (N.space ∩ (T.marked 1).space)) ∩ (T.marked 2).space = _
    ext x
    constructor
    · intro hx
      rcases hx.1 with hxL | hxB
      · exact Or.inl (hlink.symm.subset ⟨hND.subset ⟨hNL hxL.1, hx.2⟩, hxL.1⟩)
      · exact Or.inr ⟨hND.subset ⟨hxB.1, hx.2⟩, hxB.2⟩
    · rintro (hxL | hxB)
      · obtain ⟨hxD, hxN⟩ := hlink.subset hxL
        have h := hND.symm.subset hxD
        exact ⟨Or.inl ⟨hxN, T.disk_space_subset_region h.2⟩, h.2⟩
      · have h := hND.symm.subset hxB.1
        exact ⟨Or.inr ⟨h.1, hxB.2⟩, h.2⟩
  exact hrim.trans (congrArg (fun B => (L.link cs).space ∪ B) (T.disk_dual_inter_boundary s))

end PoincareMT.M76.OriginalProperDiskTriangulation
