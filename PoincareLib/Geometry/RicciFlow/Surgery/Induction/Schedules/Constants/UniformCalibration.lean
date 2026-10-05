import PoincareLib.Geometry.RicciFlow.Surgery.Singular.LimitTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Calibration.HeightRestriction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- One threshold for Theorem 11.19 and the geometric Corollary 11.36
selector, chosen before every reference manifold and both constants. -/
theorem m31M32UniformCalibration
    (L31 : RepairedSingularRegularLimitTheory.{u})
    (L32 : RepairedHornSelectionTheory.{u})
    (A : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ terminalAccuracyFactor * epsilon₀ ≤ A.epsilon₀ ∧
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
  obtain ⟨e31, he31, hA, limit⟩ := L31.limit A
  obtain ⟨e32, he32, _, selector⟩ := L32.scale_selection
  refine ⟨min e31 e32, lt_min he31 he32, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (min_le_left e31 e32)
      terminalAccuracyFactor_pos.le).trans hA
  · intro M _ _ _ _ _ _ _ _ F T H he
    exact limit H (he.trans (min_le_left e31 e32))
  · intro epsilon C analyticConstant he he0 hC hAnalytic
    apply selector epsilon C analyticConstant he
      (he0.trans (min_le_right e31 e32)) hC hAnalytic A
    exact (mul_le_mul_of_nonneg_left
      (he0.trans (min_le_left e31 e32)) terminalAccuracyFactor_pos.le).trans hA

end PoincareMT
