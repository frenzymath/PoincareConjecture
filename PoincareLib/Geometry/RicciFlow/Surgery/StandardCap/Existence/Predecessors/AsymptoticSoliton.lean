import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Limits
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem ancientAsymptoticSolitonTheory_from_predecessors (n : ℕ)
    (hP : ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution n M),
      AncientAsymptoticSolitonPredecessors K) :
    AncientAsymptoticSolitonTheory.{u} n := by
  refine ⟨?_⟩
  intro M _ _ _ _ _ _ _ _ _ K S
  exact ancientAsymptoticSolitonLimits n M K S (hP M K)

end PoincareMT
