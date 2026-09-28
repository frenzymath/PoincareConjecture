import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

def OriginalSurfacePairChart.restrict_ambient
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b)
    {U : Set X} (hU : IsOpen U) (hyU : y ∈ U) :
    OriginalSurfacePairChart e S T y b := by
  let V := C.chart.target ∩ C.chart.symm ⁻¹' U
  have hV : IsOpen V := C.chart.symm.isOpen_inter_preimage hU
  let H := C.coordinates.restr V
  have hsource : H.source = C.coordinates.source ∩ V :=
    C.coordinates.restr_source' V hV
  refine {
    chart := C.chart
    coordinates := H
    compatible := C.compatible
    center_source := C.center_source
    center_coordinates := ?_
    center_zero := C.center_zero
    source_subset := fun z hz => C.source_subset (hsource.subset hz).1
    forwardPL := C.forwardPL.mono H.open_source (fun _ hz => (hsource.subset hz).1)
    inversePL := C.inversePL.mono H.open_target (fun _ hz => hz.1)
    first_surface := fun z hz => C.first_surface z (hsource.subset hz).1
    second_surface := fun z hz => C.second_surface z (hsource.subset hz).1 }
  rw [hsource]
  refine ⟨C.center_coordinates, C.chart.map_source C.center_source, ?_⟩
  change C.chart.symm (C.chart y) ∈ U
  rwa [C.chart.left_inv C.center_source]

theorem OriginalSurfacePairChart.restrict_ambient_mem
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b)
    {U : Set X} (hU : IsOpen U) (hyU : y ∈ U) :
    ∀ z ∈ (C.restrict_ambient hU hyU).coordinates.source,
      (C.restrict_ambient hU hyU).chart.symm z ∈ U := by
  intro z hz
  have hV : IsOpen (C.chart.target ∩ C.chart.symm ⁻¹' U) :=
    C.chart.symm.isOpen_inter_preimage hU
  change z ∈ (C.coordinates.restr _).source at hz
  rw [C.coordinates.restr_source' _ hV] at hz
  exact hz.2.2

theorem OriginalSurfacePairChart.exists_interior_region_model
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T R : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b) (hyR : y ∈ interior R) :
    ∃ (D : OriginalSurfacePairChart e S T y b) (A : Set (ℝ × ℝ)),
      ∀ z ∈ D.coordinates.source, D.chart.symm z ∈ R ↔ (D.coordinates z).1 ∈ A := by
  refine ⟨C.restrict_ambient isOpen_interior hyR, univ, ?_⟩
  intro z hz
  exact iff_of_true (interior_subset (C.restrict_ambient_mem isOpen_interior hyR z hz))
    (mem_univ _)

end PoincareConjecture.M76
