import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

private def crossingCoordinateSwap : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) where
  toFun z := ((z.2,z.1.2),z.1.1)
  invFun z := ((z.2,z.1.2),z.1.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def OriginalSurfacePairChart.swap
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {S T : Set X} {y : X} {boundary : Bool}
    (C : OriginalSurfacePairChart e S T y boundary) :
    OriginalSurfacePairChart e T S y boundary := by
  let P := crossingCoordinateSwap
  let H := C.coordinates.trans P.toHomeomorph.toOpenPartialHomeomorph
  have hsource : H.source = C.coordinates.source := by
    simp [H]
  have hforward : LocallyPiecewiseAffineOn H H.source := by
    have hh := (locallyPiecewiseAffineOn_affine
      P.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp C.forwardPL
    simpa [H] using hh
  have hinverse : LocallyPiecewiseAffineOn H.symm H.target := by
    have hh := C.inversePL.comp (locallyPiecewiseAffineOn_affine
      P.symm.toContinuousLinearMap.toContinuousAffineMap isOpen_univ)
    simpa [H] using hh
  refine {
    chart := C.chart
    coordinates := H
    compatible := C.compatible
    center_source := C.center_source
    center_coordinates := hsource.symm ▸ C.center_coordinates
    center_zero := ?_
    source_subset := hsource ▸ C.source_subset
    forwardPL := hforward
    inversePL := hinverse
    first_surface := ?_
    second_surface := ?_ }
  · change P (C.coordinates (C.chart y)) = 0
    rw [C.center_zero]
    exact P.map_zero
  · intro z hz
    exact C.second_surface z (hsource ▸ hz)
  · intro z hz
    exact C.first_surface z (hsource ▸ hz)

end PoincareConjecture.M76
