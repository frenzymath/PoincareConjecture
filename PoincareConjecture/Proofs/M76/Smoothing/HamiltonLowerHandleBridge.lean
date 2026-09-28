import PoincareConjecture.Proofs.M76.Smoothing.HamiltonCairnsBridge
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonHandleAssembly










set_option autoImplicit false

namespace PoincareConjecture.M76

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]




theorem smoothingConclusion_of_lower_handle_cases
    (P : SmoothingBridgeInput (M := M))
    (indexZero : HasHamiltonChartHandleStraightening (Fin 3 → ℝ) ∅)
    (indexOne : ∀ J : Finset (Fin 3), J.card = 1 →
      HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J)
    (indexTwo : ∀ J : Finset (Fin 3), J.card = 2 →
      HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J) :
    M76SmoothingConclusion P :=
  smoothingConclusion_of_supportedPLOverlapStraightening P
    (hasSupportedPLOverlapStraightening_of_lower_handle_cases (by simp)
      indexZero indexOne indexTwo)

end PoincareConjecture.M76
