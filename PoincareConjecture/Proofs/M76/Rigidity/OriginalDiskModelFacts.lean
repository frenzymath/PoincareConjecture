import PoincareConjecture.Proofs.M76.Rigidity.OriginalProperDiskTriangulation
import PoincareConjecture.Proofs.M76.Rigidity.IntrinsicDiskFaces
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

theorem marked_finite (i : Fin 4) : (T.marked i).faces.Finite :=
  T.finite.subset (T.marked_le i)

theorem inverse_injOn : InjOn (fun x => (T.inverse x : X)) T.ambient.space := by
  intro x hx y hy hxy
  have h : T.model.symm ⟨x, hx⟩ = T.model.symm ⟨y, hy⟩ := by
    apply Subtype.ext
    exact (T.inverse_eq ⟨x, hx⟩).symm.trans (hxy.trans (T.inverse_eq ⟨y, hy⟩))
  exact congrArg Subtype.val (T.model.symm.injective h)

theorem inverse_mem_region_iff {x : T.index → ℝ × V3} (hx : x ∈ T.ambient.space) :
    (T.inverse x : X) ∈ R ↔ x ∈ (T.marked 0).space := by
  rw [T.region_space]
  exact original_model_mem_image_iff T.model T.graph T.inverse T.model_eq T.inverse_eq
    (T.region_interior.trans interior_subset) ⟨x, hx⟩

theorem inverse_mem_disk_iff {x : T.index → ℝ × V3} (hx : x ∈ T.ambient.space) :
    (T.inverse x : X) ∈ j '' D ↔ x ∈ (T.marked 2).space := by
  rw [T.disk_space]
  apply original_model_mem_image_iff T.model T.graph T.inverse T.model_eq T.inverse_eq
    (z := ⟨x, hx⟩)
  rintro _ ⟨z, hz, rfl⟩
  exact interior_subset (T.region_interior (T.disk_in_region hz))

theorem parameter_disk_point {x : T.index → ℝ × V3} (hx : x ∈ (T.marked 2).space) :
    T.parameter x ∈ D ∧ j (T.parameter x) = (T.inverse x : X) :=
  disk_parameter_eq_model_inverse T.model T.graph T.inverse T.model_eq T.inverse_eq
    (fun _ hz => interior_subset (T.region_interior (T.disk_in_region hz)))
    T.parameter T.parameter_original (T.disk_space.subset hx)

theorem disk_face_card_le {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) : s.card ≤ 3 :=
  (intrinsic_disk_face_dimensions (T.marked 2) (T.marked_finite 2)
    T.graph j T.parameter T.disk_space T.parameter_original
    (fun t ht => T.parameter_affine t (T.marked_le 2 ht))).1 s hs

theorem exists_disk_triangle_coface {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) :
    ∃ t ∈ (T.marked 2).faces, s ⊆ t ∧ t.card = 3 :=
  (intrinsic_disk_face_dimensions (T.marked 2) (T.marked_finite 2)
    T.graph j T.parameter T.disk_space T.parameter_original
    (fun t ht => T.parameter_affine t (T.marked_le 2 ht))).2 s hs

def height (p : (T.marked 2).vertices) (x : T.index → ℝ × V3) : ℝ :=
  T.weight (T.chart_index p) * (T.chart (T.chart_index p) (T.inverse x)).2

open Classical in

theorem height_affine (p : (T.marked 2).vertices) :
    (T.ambient.closedStar p).AffineOnFaces (T.height p) := by
  let a : C3 →L[ℝ] ℝ :=
    T.weight (T.chart_index p) • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  exact (T.star_affine p).postcomp a.toContinuousAffineMap

open Classical in

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

end PoincareConjecture.M76.OriginalProperDiskTriangulation
