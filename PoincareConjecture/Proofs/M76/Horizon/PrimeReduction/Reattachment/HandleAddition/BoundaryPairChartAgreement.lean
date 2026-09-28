import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.Restriction

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem OriginalSurfacePairChart.exists_boundary_model_of_agreement
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T T' R W : Set X} {y : X}
    (C : OriginalSurfacePairChart e S T y true)
    (hW : IsOpen W) (hyW : y ∈ W)
    (hagree : ∀ z ∈ W,z ∈ T' ↔ z ∈ T)
    (hR : ∀ z ∈ C.coordinates.source,C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    (hfront : ∀ z ∈ C.coordinates.source,
      C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0) :
    ∃ C' : OriginalSurfacePairChart e S T' y true,
      (∀ z ∈ C'.coordinates.source,C'.chart.symm z ∈ R ↔ 0 ≤ (C'.coordinates z).1.2) ∧
      ∀ z ∈ C'.coordinates.source,
        C'.chart.symm z ∈ frontier R ↔ (C'.coordinates z).1.2 = 0 := by
  let A := C.restrict_ambient hW hyW
  have hsub : A.coordinates.source ⊆ C.coordinates.source := by
    intro z hz
    exact hz.1
  let C' : OriginalSurfacePairChart e S T' y true := {
    chart := A.chart
    coordinates := A.coordinates
    compatible := A.compatible
    center_source := A.center_source
    center_coordinates := A.center_coordinates
    center_zero := A.center_zero
    source_subset := A.source_subset
    forwardPL := A.forwardPL
    inversePL := A.inversePL
    first_surface := A.first_surface
    second_surface := fun z hz =>
      (hagree _ (C.restrict_ambient_mem hW hyW z hz)).trans (A.second_surface z hz) }
  exact ⟨C',fun z hz => hR z (hsub hz),fun z hz => hfront z (hsub hz)⟩

end PoincareConjecture.M76
