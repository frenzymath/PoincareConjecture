import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.Vertices

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem original_PL_motion_trans_compatible_chart
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (F : X ≃ₜ X) (B : OpenPartialHomeomorph X V3)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) :
    ∀ i, (e i).symm.trans (F.toOpenPartialHomeomorph.trans B) ∈
      piecewiseAffineGroupoid V3 := by
  intro i
  let D := (e i).symm.trans (F.toOpenPartialHomeomorph.trans B)
  apply (mem_piecewiseAffineGroupoid_iff_forward D).mpr
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  obtain ⟨j, hj⟩ := hcover (F ((e i).symm x))
  let A := (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j))
  let C := (e j).symm.trans B
  have hxA : x ∈ A.source := ⟨hx.1, mem_univ _, hj⟩
  have hcomp := ((mem_piecewiseAffineGroupoid_iff_forward C).mp (hB j)).comp
    ((mem_piecewiseAffineGroupoid_iff_forward A).mp (hF i j))
  refine ⟨A.source, hxA, ?_⟩
  have hsub : D.source ∩ A.source ⊆ A.source ∩ A ⁻¹' C.source := by
    intro y hy
    have hyj : F ((e i).symm y) ∈ (e j).source := hy.2.2.2
    refine ⟨hy.2, (e j).map_source hyj, ?_⟩
    change (e j).symm ((e j) (F ((e i).symm y))) ∈ B.source
    rw [(e j).left_inv hyj]
    exact hy.1.2.2
  apply (hcomp.mono (D.open_source.inter A.open_source) hsub).congr
  intro y hy
  have hyj : F ((e i).symm y) ∈ (e j).source := hy.2.2.2
  change B ((e j).symm ((e j) (F ((e i).symm y)))) = B (F ((e i).symm y))
  rw [(e j).left_inv hyj]

def OriginalSurfacePairChart.image_first_of_preserving_second
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (F : X ≃ₜ X)
    (hFinv : ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hT : F ⁻¹' T = T) :
    OriginalSurfacePairChart e (F '' S) T (F y) b where
  chart := F.symm.toOpenPartialHomeomorph.trans C.chart
  coordinates := C.coordinates
  compatible := original_PL_motion_trans_compatible_chart e hcover F.symm C.chart
    hFinv C.compatible
  center_source := ⟨mem_univ _, by simpa using C.center_source⟩
  center_coordinates := by simpa using C.center_coordinates
  center_zero := by simpa using C.center_zero
  source_subset := fun z hz => ⟨C.source_subset hz, mem_univ _⟩
  forwardPL := C.forwardPL
  inversePL := C.inversePL
  first_surface := by
    intro z hz
    change F (C.chart.symm z) ∈ F '' S ↔ _
    rw [F.injective.mem_set_image]
    exact C.first_surface z hz
  second_surface := by
    intro z hz
    change F (C.chart.symm z) ∈ T ↔ _
    have hmem : F (C.chart.symm z) ∈ T ↔ C.chart.symm z ∈ T := by
      change C.chart.symm z ∈ F ⁻¹' T ↔ _
      rw [hT]
    exact hmem.trans (C.second_surface z hz)

end PoincareConjecture.M76
