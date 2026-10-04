import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Calibration.Calibration

/-!
# The same calibrated terminal limit

Apply M45's stored M31 service and retain its actual Appendix A accuracy
bound. The horn wrapper uses exactly that limit. This supplies only the
limit and calibration portion of M33's bridge; the regular history, analytic
estimates and deep-horn application remain M48 construction obligations.
Sources: Morgan--Tian Theorem 11.19 and Lemma 11.28, pp. 279-284.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

/-- Choose the supplied singular limit once, preserving its identity in
the horn data and the bound for the stored Appendix A service. -/
theorem m48CalibratedLimit
    (S : RepairedControlledSchedulesData.{u})
    {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions G T M)
    (he : H.epsilon ≤ S.calibration.common_epsilon) :
    ∃ L : RepairedSingularRegularLimitData H,
      ∃ N : RepairedHornSelectionData H,
        N.limit = L ∧ terminalAccuracyFactor * H.epsilon ≤ S.calibration.appendixA.epsilon₀ := by
  obtain ⟨L⟩ := S.calibration.singular_limit H he
  exact ⟨L, ⟨L⟩, rfl, S.appendixA_accuracy he⟩

end PoincareMT
