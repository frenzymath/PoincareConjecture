import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.RetainedCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.ChartSymmetry



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem OriginalSurfacePairChart.swap_boundary_region
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T R : Set X} {y : X}
    (C : OriginalSurfacePairChart e S T y true)
    (hR : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    (hfront : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0) :
    ∃ C' : OriginalSurfacePairChart e T S y true,
      (∀ z ∈ C'.coordinates.source, C'.chart.symm z ∈ R ↔ 0 ≤ (C'.coordinates z).1.2) ∧
      ∀ z ∈ C'.coordinates.source, C'.chart.symm z ∈ frontier R ↔ (C'.coordinates z).1.2 = 0 := by
  exact ⟨C.swap, (fun z hz ↦ hR z hz.1), fun z hz ↦ hfront z hz.1⟩

theorem OriginalSurfacePairChart.exists_boundary_of_local_agreement
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {S T S' T' W R : Set X} {y : X}
    (C : OriginalSurfacePairChart e S T y true)
    (hR : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔
      0 ≤ (C.coordinates z).1.2)
    (hfront : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔
      (C.coordinates z).1.2 = 0)
    (hW : IsOpen W) (hyW : y ∈ W)
    (hS : ∀ z ∈ W, z ∈ S' ↔ z ∈ S)
    (hT : ∀ z ∈ W, z ∈ T' ↔ z ∈ T) :
    ∃ C' : OriginalSurfacePairChart e S' T' y true,
      (∀ z ∈ C'.coordinates.source, C'.chart.symm z ∈ R ↔
        0 ≤ (C'.coordinates z).1.2) ∧
      (∀ z ∈ C'.coordinates.source, C'.chart.symm z ∈ frontier R ↔
        (C'.coordinates z).1.2 = 0) ∧
      ∀ z ∈ C'.coordinates.source, C'.chart.symm z ∈ W := by
  let V := C.chart '' (C.chart.source ∩ W)
  have hV : IsOpen V := C.chart.isOpen_image_of_subset_source
    (C.chart.open_source.inter hW) inter_subset_left
  have hVW (z : Fin 3 → ℝ) (hz : z ∈ V) : C.chart.symm z ∈ W := by
    obtain ⟨x, hx, rfl⟩ := hz
    rw [C.chart.left_inv hx.1]
    exact hx.2
  let C' : OriginalSurfacePairChart e S' T' y true := {
    chart := C.chart
    coordinates := C.coordinates.restrOpen V hV
    compatible := C.compatible
    center_source := C.center_source
    center_coordinates := ⟨C.center_coordinates, ⟨y, ⟨C.center_source, hyW⟩, rfl⟩⟩
    center_zero := C.center_zero
    source_subset := fun _ hz ↦ C.source_subset hz.1
    forwardPL := C.forwardPL.mono (C.coordinates.restrOpen V hV).open_source inter_subset_left
    inversePL := C.inversePL.mono (C.coordinates.restrOpen V hV).open_target inter_subset_left
    first_surface := fun z hz ↦ (hS _ (hVW z hz.2)).trans (C.first_surface z hz.1)
    second_surface := fun z hz ↦ (hT _ (hVW z hz.2)).trans (C.second_surface z hz.1) }
  exact ⟨C', (fun z hz ↦ hR z hz.1), (fun z hz ↦ hfront z hz.1), fun z hz ↦ hVW z hz.2⟩

theorem original_pair_charts_after_local_replacement
    {X ι E : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R W : Set X}
    {S T : Set E} {f g k : E → X}
    (hW : IsOpen W) (hinside : (g '' T) ∩ (k '' S) ⊆ W)
    (hagree : ∀ z ∈ W, z ∈ k '' S ↔ z ∈ f '' S)
    (hkeep : EqOn k f (S ∩ k ⁻¹' (g '' T)))
    (hboundary : ∀ x ∈ S, f x ∈ g '' T → f x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (f '' S) (g '' T) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ S, f x ∈ g '' T → f x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f '' S) (g '' T) (f x) false)) :
    (∀ x ∈ S, k x ∈ g '' T → k x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (k '' S) (g '' T) (k x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) ∧
    ∀ x ∈ S, k x ∈ g '' T → k x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (k '' S) (g '' T) (k x) false) := by
  constructor
  · intro x hx hxg hxfront
    have hv := hkeep ⟨hx, hxg⟩
    have hxW := hinside ⟨hxg, ⟨x, hx, rfl⟩⟩
    rw [hv] at hxg hxfront hxW ⊢
    obtain ⟨B, hBR, hBF⟩ := hboundary x hx hxg hxfront
    obtain ⟨B', hB'R, hB'F, _⟩ := B.exists_boundary_of_local_agreement hBR hBF hW hxW
      hagree (fun _ _ ↦ Iff.rfl)
    exact ⟨B', hB'R, hB'F⟩
  · intro x hx hxg hxint
    have hv := hkeep ⟨hx, hxg⟩
    have hxW := hinside ⟨hxg, ⟨x, hx, rfl⟩⟩
    rw [hv] at hxg hxint hxW ⊢
    obtain ⟨B⟩ := hinterior x hx hxg hxint
    obtain ⟨B', _⟩ := B.exists_of_local_agreement hW hxW hagree (fun _ _ ↦ Iff.rfl)
    exact ⟨B'⟩

end PoincareConjecture.M76
