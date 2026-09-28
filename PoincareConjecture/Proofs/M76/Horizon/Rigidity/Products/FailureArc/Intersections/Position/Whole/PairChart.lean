import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

structure OriginalSurfacePairChart
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (S T : Set X) (y : X) (boundary : Bool) where
  chart : OpenPartialHomeomorph X (Fin 3 → ℝ)
  coordinates : OpenPartialHomeomorph (Fin 3 → ℝ) ((ℝ × ℝ) × ℝ)
  compatible : ∀ i, (e i).symm.trans chart ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)
  center_source : y ∈ chart.source
  center_coordinates : chart y ∈ coordinates.source
  center_zero : coordinates (chart y) = 0
  source_subset : coordinates.source ⊆ chart.target
  forwardPL : LocallyPiecewiseAffineOn coordinates coordinates.source
  inversePL : LocallyPiecewiseAffineOn coordinates.symm coordinates.target
  first_surface : ∀ z ∈ coordinates.source, chart.symm z ∈ S ↔
    (coordinates z).2 = 0 ∧ (boundary = true → 0 ≤ (coordinates z).1.2)
  second_surface : ∀ z ∈ coordinates.source, chart.symm z ∈ T ↔
    (coordinates z).1.1 = 0 ∧ (boundary = true → 0 ≤ (coordinates z).1.2)

def OriginalSurfacePairChart.of_interior_planes
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T : Set X} {y : X}
    (B : OpenPartialHomeomorph X (Fin 3 → ℝ))
    (H : OpenPartialHomeomorph (Fin 3 → ℝ) ((ℝ × ℝ) × ℝ))
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (hyB : y ∈ B.source) (hyH : B y ∈ H.source) (hzero : H (B y) = 0)
    (hsource : H.source ⊆ B.target)
    (hPL : LocallyPiecewiseAffineOn H H.source)
    (hInv : LocallyPiecewiseAffineOn H.symm H.target)
    (hS : ∀ z ∈ H.source, B.symm z ∈ S ↔ (H z).2 = 0)
    (hT : ∀ z ∈ H.source, B.symm z ∈ T ↔ (H z).1.1 = 0) :
    OriginalSurfacePairChart e S T y false where
  chart := B
  coordinates := H
  compatible := hB
  center_source := hyB
  center_coordinates := hyH
  center_zero := hzero
  source_subset := hsource
  forwardPL := hPL
  inversePL := hInv
  first_surface := by simpa using hS
  second_surface := by simpa using hT

end PoincareConjecture.M76
