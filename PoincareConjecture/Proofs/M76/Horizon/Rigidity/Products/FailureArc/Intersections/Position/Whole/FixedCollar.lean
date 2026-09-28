import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

def OriginalSurfacePairChart.image_first_of_fixed_neighborhood
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b) (F : X ≃ₜ X)
    {W : Set X} (hW : IsOpen W) (hyW : y ∈ W) (hfix : EqOn F id W) :
    OriginalSurfacePairChart e (F '' S) T y b := by
  let U := C.chart.target ∩ C.chart.symm ⁻¹' W
  have hU : IsOpen U := C.chart.symm.isOpen_inter_preimage hW
  let H := C.coordinates.restr U
  have hsource : H.source = C.coordinates.source ∩ U :=
    C.coordinates.restr_source' U hU
  have hfirst (z : Fin 3 → ℝ) (hz : z ∈ H.source) :
      C.chart.symm z ∈ F '' S ↔ C.chart.symm z ∈ S := by
    have hzW : C.chart.symm z ∈ W := (hsource.subset hz).2.2
    constructor
    · rintro ⟨w, hw, heq⟩
      exact F.injective (heq.trans (hfix hzW).symm) ▸ hw
    · exact fun hw => ⟨C.chart.symm z, hw, hfix hzW⟩
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
    first_surface := fun z hz => (hfirst z hz).trans (C.first_surface z (hsource.subset hz).1)
    second_surface := fun z hz => C.second_surface z (hsource.subset hz).1 }
  rw [hsource]
  refine ⟨C.center_coordinates, C.chart.map_source C.center_source, ?_⟩
  change C.chart.symm (C.chart y) ∈ W
  rwa [C.chart.left_inv C.center_source]

end PoincareConjecture.M76
