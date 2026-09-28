import PoincareConjecture.Proofs.M32.Calibration

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M45

theorem commonThresholdServices
    (h31 : RepairedSingularRegularLimitTheory.{u})
    (h32 : RepairedHornSelectionTheory.{u})
    (A : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ terminalAccuracyFactor * epsilon₀ ≤ A.epsilon₀ ∧
      2 * epsilon₀ ≤ 1 / 200 ∧
      (∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ},
        ∀ H : SingularTimeAssumptions F T M,
          H.epsilon ≤ epsilon₀ → Nonempty (RepairedSingularRegularLimitData H)) ∧
      (∀ epsilon C analyticConstant : ℝ,
        0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → 0 < analyticConstant →
        Nonempty (M32DeepHornScaleSelection.{u} epsilon C analyticConstant)) := by
  obtain ⟨epsilon₀, hpos, hA, hlimit, hselector⟩ :=
    m31M32UniformCalibration h31 h32 A
  have htwo : 2 * epsilon₀ ≤ terminalAccuracyFactor * epsilon₀ :=
    mul_le_mul_of_nonneg_right two_le_terminalAccuracyFactor hpos.le
  exact ⟨epsilon₀, hpos, hA, htwo.trans (hA.trans A.epsilon₀_le_one_two_hundred),
    hlimit, hselector⟩

end PoincareConjecture.M45
