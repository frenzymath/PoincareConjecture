import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Constants.UniformCalibration

/-!
# Common singular-limit and horn-selection threshold

Morgan--Tian, Section 15.1.1, pp. 354-355, uses Lemma 11.28 and
Corollary 11.36 at a common accuracy. This applies the existing lower
milestone construction and records Appendix A's numerical upper bound.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M45

/-- Lemma 11.28 and Corollary 11.36, as used on pp. 354-355, with
the actual Appendix A threshold retained before all later constants. -/
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

end PoincareMT.M45
