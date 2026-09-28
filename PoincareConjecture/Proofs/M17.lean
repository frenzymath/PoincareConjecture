import PoincareConjecture.Statements.M17BlowupSetup
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Rescaling.Construction









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



















theorem ancientBlowupSequenceSetup (n : ℕ)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ)
    (tau_pos : ∀ k, 0 < tau k)
    (tau_tendsto : Filter.Tendsto tau Filter.atTop Filter.atTop)
    (hM10 : AncientReducedVolumeMinimumProvider K)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientBlowupSetupConclusion K reference tau := by
  exact horizon_ancientBlowupSequenceSetup n M K reference tau tau_pos
    tau_tendsto hM10 hM13


theorem ancientBlowupSequenceSetupTheory (n : ℕ)
    (hM10 : ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution n M) (_reference : M),
      AncientReducedVolumeMinimumProvider K)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientBlowupSetupTheory.{u} n := by
  refine ⟨?_⟩
  intro M _ _ _ _ _ _ _ _ _ K reference tau tau_pos tau_tendsto
  exact ancientBlowupSequenceSetup n M K reference tau tau_pos tau_tendsto
    (hM10 M K reference) hM13

end PoincareConjecture
