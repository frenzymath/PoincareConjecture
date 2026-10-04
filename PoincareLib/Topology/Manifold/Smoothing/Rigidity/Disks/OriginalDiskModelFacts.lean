import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalProperDiskTriangulation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Simplicial.IntrinsicDiskFaces
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Regions.OriginalBoundaryMarks

/-!
# Literal parameters and heights on the original disk model

The same inverse transports full marked membership. Its original square
parameter gives disk purity, while the fixed chart labels give affine
heights with precisely the whole disk as their zero set in the region.
See rigidity018, section4 and Hudson1969, pp.12--19, 58--63.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

/-- Every retained marked complex is finite. See rigidity018, section2. -/
theorem marked_finite (i : Fin 4) : (T.marked i).faces.Finite :=
  T.finite.subset (T.marked_le i)

/-- The actual original inverse is injective on the whole modeled
carrier. See rigidity018, section4. -/
theorem inverse_injOn : InjOn (fun x => (T.inverse x : X)) T.ambient.space := by
  intro x hx y hy hxy
  have h : T.model.symm ⟨x, hx⟩ = T.model.symm ⟨y, hy⟩ := by
    apply Subtype.ext
    exact (T.inverse_eq ⟨x, hx⟩).symm.trans (hxy.trans (T.inverse_eq ⟨y, hy⟩))
  exact congrArg Subtype.val (T.model.symm.injective h)

/-- Membership in the complete original region is exactly membership
in its retained full mark. See rigidity018, sections2--4. -/
theorem inverse_mem_region_iff {x : T.index → ℝ × V3} (hx : x ∈ T.ambient.space) :
    (T.inverse x : X) ∈ R ↔ x ∈ (T.marked 0).space := by
  rw [T.region_space]
  exact original_model_mem_image_iff T.model T.graph T.inverse T.model_eq T.inverse_eq
    (T.region_interior.trans interior_subset) ⟨x, hx⟩

/-- The literal original disk image is exactly the retained full disk
mark on the entire modeled carrier. See rigidity018, sections2--4. -/
theorem inverse_mem_disk_iff {x : T.index → ℝ × V3} (hx : x ∈ T.ambient.space) :
    (T.inverse x : X) ∈ j '' D ↔ x ∈ (T.marked 2).space := by
  rw [T.disk_space]
  apply original_model_mem_image_iff T.model T.graph T.inverse T.model_eq T.inverse_eq
    (z := ⟨x, hx⟩)
  rintro _ ⟨z, hz, rfl⟩
  exact interior_subset (T.region_interior (T.disk_in_region hz))

/-- Every point of the same whole disk mark retains its original
square parameter and actual original inverse value. See rigidity018. -/
theorem parameter_disk_point {x : T.index → ℝ × V3} (hx : x ∈ (T.marked 2).space) :
    T.parameter x ∈ D ∧ j (T.parameter x) = (T.inverse x : X) :=
  disk_parameter_eq_model_inverse T.model T.graph T.inverse T.model_eq T.inverse_eq
    (fun _ hz => interior_subset (T.region_interior (T.disk_in_region hz)))
    T.parameter T.parameter_original (T.disk_space.subset hx)

/-- The original square parameter bounds every actual disk face.
See rigidity017, section1 and rigidity018, section4. -/
theorem disk_face_card_le {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) : s.card ≤ 3 :=
  (intrinsic_disk_face_dimensions (T.marked 2) (T.marked_finite 2)
    T.graph j T.parameter T.disk_space T.parameter_original
    (fun t ht => T.parameter_affine t (T.marked_le 2 ht))).1 s hs

/-- The original square parameter constructs a triangular coface of
every actual disk face, in the same mark. See rigidity018, section4. -/
theorem exists_disk_triangle_coface {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) :
    ∃ t ∈ (T.marked 2).faces, s ⊆ t ∧ t.card = 3 :=
  (intrinsic_disk_face_dimensions (T.marked 2) (T.marked_finite 2)
    T.graph j T.parameter T.disk_space T.parameter_original
    (fun t ht => T.parameter_affine t (T.marked_le 2 ht))).2 s hs

/-- The literal labelled normal coordinate of the selected original
chart at a disk vertex. See rigidity016 and rigidity018, section4. -/
def height (p : (T.marked 2).vertices) (x : T.index → ℝ × V3) : ℝ :=
  T.weight (T.chart_index p) * (T.chart (T.chart_index p) (T.inverse x)).2

open Classical in
/-- A fixed scalar normal projection is affine on every whole selected
star face. No regularity of a product chart is used. See rigidity018. -/
theorem height_affine (p : (T.marked 2).vertices) :
    (T.ambient.closedStar p).AffineOnFaces (T.height p) := by
  let a : C3 →L[ℝ] ℝ :=
    T.weight (T.chart_index p) • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  exact (T.star_affine p).postcomp a.toContinuousAffineMap

open Classical in
/-- The entire region part of a selected star has exactly the whole
original disk mark as the height zero set. See rigidity018, section4. -/
theorem height_eq_zero_iff (p : (T.marked 2).vertices)
    {x : T.index → ℝ × V3} (hx : x ∈ (T.ambient.closedStar p).space)
    (hxR : x ∈ (T.marked 0).space) : T.height p x = 0 ↔ x ∈ (T.marked 2).space := by
  have hstar : T.ambient.closedStar p ≤ T.ambient := fun _ ht => ht.1
  have hxK : x ∈ T.ambient.space :=
    SimplicialComplex.space_subset_of_le hstar hx
  have hxsource := T.star_source p hx
  have hxregion : (T.inverse x : X) ∈ R := (T.inverse_mem_region_iff hxK).mpr hxR
  rw [height, mul_eq_zero, or_iff_right (T.weight_nonzero (T.chart_index p))]
  apply Iff.trans _ (T.inverse_mem_disk_iff hxK)
  rcases T.chart_model (T.chart_index p) with hi | hb
  · exact (hi.2 _ hxsource).symm
  · have hnonneg := (hb.1 _ hxsource).mp hxregion
    exact ⟨fun h => (hb.2 _ hxsource).mpr ⟨hnonneg, h⟩,
      fun h => ((hb.2 _ hxsource).mp h).2⟩

end PoincareMT.M76.OriginalProperDiskTriangulation
