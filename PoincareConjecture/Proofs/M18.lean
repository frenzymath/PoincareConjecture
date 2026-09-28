import PoincareConjecture.Statements.M18AsymptoticSoliton
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Limits









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture






































theorem ancientAsymptoticSolitonLimits
    (n : ℕ)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    AncientAsymptoticSolitonConclusion S := by
  exact horizon_ancientAsymptoticSolitonLimits n M K S P




theorem ancientAsymptoticSolitonLimits_of_setup
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    {K : AncientKappaSolution n M} {reference : M} {tau : ℕ → ℝ}
    (S : AncientBlowupSetup K reference tau)
    (P : AncientAsymptoticSolitonPredecessors K) :
    AncientAsymptoticSolitonConclusion S.sequence :=
  ancientAsymptoticSolitonLimits n M K S.sequence P




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

end PoincareConjecture
