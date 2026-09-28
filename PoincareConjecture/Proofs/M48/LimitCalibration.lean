import PoincareConjecture.Proofs.M45.Calibration

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

theorem m48CalibratedLimit
    (S : RepairedControlledSchedulesData.{u})
    {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions G T M)
    (he : H.epsilon ≤ S.calibration.common_epsilon) :
    ∃ L : RepairedSingularRegularLimitData H,
      ∃ N : RepairedHornSelectionData H,
        N.limit = L ∧
          terminalAccuracyFactor * H.epsilon ≤ S.calibration.appendixA.epsilon₀ := by
  obtain ⟨L⟩ := S.calibration.singular_limit H he
  exact ⟨L, ⟨L⟩, rfl, S.appendixA_accuracy he⟩

end PoincareConjecture
