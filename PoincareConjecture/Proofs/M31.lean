import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Assembly.Completion
import PoincareConjecture.Statements.M31SingularRegularLimit
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M31.RegularCanonical

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m31SingularRegularLimit (P04 : RicciFlowCurvatureTheory.{u}) :
    ∀ A : RepairedNeckCapTopologyTheory.{u},
      ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ terminalAccuracyFactor * epsilon₀ ≤ A.epsilon₀ ∧
        ∀ {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M]
          {F : GeneralizedRicciFlowData.{u}} {T : ℝ},
          ∀ H : SingularTimeAssumptions F T M,
            H.epsilon ≤ epsilon₀ →
              Nonempty (RepairedSingularRegularLimitData H) :=
  (horizon_m31SingularRegularLimit P04).limit

theorem m31SingularRegularLimitTheory : RepairedSingularRegularLimitTheory.{u} := by
  exact ⟨m31SingularRegularLimit ricciFlowCurvatureTheory⟩

end PoincareConjecture
