import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Handles.HamiltonCairnsBridge
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonHandleAssembly

/-!
# The smoothing conclusion from the three remaining handle cases

All finite relative assembly, Alexander region balls, triangulation and
Cairns smoothing steps are supplied by checked proofs. Only Hamilton's
three lower-index geometric constructions remain hypotheses.
See Hamilton 1976, pp. 64--69 and M76 derivations319--320 and330.
-/

set_option autoImplicit false

namespace PoincareMT.M76

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- The frozen smoothing conclusion follows from exactly the three
lower-index chart-handle statements. No extra hypothesis is introduced
into the milestone statement. See Hamilton pp.64--69 and derivation330. -/
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

end PoincareMT.M76
