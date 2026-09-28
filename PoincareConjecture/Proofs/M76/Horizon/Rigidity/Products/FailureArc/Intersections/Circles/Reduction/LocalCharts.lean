import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem OriginalSurfacePairChart.exists_of_local_agreement
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {S T S' T' W : Set X} {y : X} {boundary : Bool}
    (C : OriginalSurfacePairChart e S T y boundary)
    (hW : IsOpen W) (hyW : y ∈ W)
    (hS : ∀ z ∈ W, z ∈ S' ↔ z ∈ S)
    (hT : ∀ z ∈ W, z ∈ T' ↔ z ∈ T) :
    ∃ C' : OriginalSurfacePairChart e S' T' y boundary,
      ∀ z ∈ C'.coordinates.source, C'.chart.symm z ∈ W := by
  let V := C.chart '' (C.chart.source ∩ W)
  have hV : IsOpen V := C.chart.isOpen_image_of_subset_source
    (C.chart.open_source.inter hW) inter_subset_left
  have hVW (z : Fin 3 → ℝ) (hz : z ∈ V) : C.chart.symm z ∈ W := by
    obtain ⟨x,hx,rfl⟩ := hz
    rw [C.chart.left_inv hx.1]
    exact hx.2
  let C' : OriginalSurfacePairChart e S' T' y boundary := {
    chart := C.chart
    coordinates := C.coordinates.restrOpen V hV
    compatible := C.compatible
    center_source := C.center_source
    center_coordinates := ⟨C.center_coordinates,⟨y,⟨C.center_source,hyW⟩,rfl⟩⟩
    center_zero := C.center_zero
    source_subset := fun _ hz => C.source_subset hz.1
    forwardPL := C.forwardPL.mono (C.coordinates.restrOpen V hV).open_source inter_subset_left
    inversePL := C.inversePL.mono (C.coordinates.restrOpen V hV).open_target inter_subset_left
    first_surface := fun z hz => (hS _ (hVW z hz.2)).trans (C.first_surface z hz.1)
    second_surface := fun z hz => (hT _ (hVW z hz.2)).trans (C.second_surface z hz.1) }
  exact ⟨C',fun z hz => hVW z hz.2⟩

end PoincareConjecture.M76
