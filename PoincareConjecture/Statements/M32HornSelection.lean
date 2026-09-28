import PoincareConjecture.Definitions.M32HornSelection
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.M19TwoDimensionalClassification
import PoincareConjecture.Statements.M25NeckCapTopology
import PoincareConjecture.Statements.M29GeneralizedDistance
import PoincareConjecture.Statements.M30ControlledBlowupLimits
import PoincareConjecture.Statements.M31SingularRegularLimit















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


structure RepairedHornSelectionPredecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m19_round : ∀ {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
    [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
    [T2Space N] [T3Space N] [SecondCountableTopology N]
    [ConnectedSpace N],
    ∀ K : AncientKappaSolution 2 N,
      Nonempty (TwoDimensionalAncientRoundCertificate K)
  m29 : RepairedGeneralizedBoundedDistanceTheory.{u}
  m30 : RepairedControlledBlowupLimitTheory.{u}

structure RepairedHornSelectionTheory : Prop where

  providers : RepairedHornSelectionPredecessors.{u}


  deep_horn : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ (r₀ C analyticConstant rho delta : ℝ),
        0 < r₀ → 0 < C → 0 < analyticConstant →
        0 < rho → rho < r₀ → 0 < delta →
        ∀ (A : RepairedNeckCapTopologyTheory.{u}),
          terminalAccuracyFactor * epsilon ≤ A.epsilon₀ →
          ∃ h : ℝ, 0 < h ∧ h ≤ min (rho * delta) (rho / (2 * C)) ∧
            ∀ {F' : GeneralizedRicciFlowData.{u}} {T' : ℝ}
              {N : Type u} [TopologicalSpace N]
              [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
              [IsManifold (𝓡 3) ∞ N] [MeasurableSpace N] [BorelSpace N]
              [T2Space N] [T3Space N] [SecondCountableTopology N],
              ∀ H' : SingularTimeAssumptions F' T' N,
                H'.r₀ = r₀ → H'.epsilon = epsilon → H'.constant = C →
                H'.analytic_constant = analyticConstant →
                ∀ Q : SingularLimitConclusion H',
                  ∀ horn : StrongHorn Q.extension (terminalAccuracyFactor * H'.epsilon),
                    HornBoundaryBelow horn (rho / (2 * H'.constant)) →
                      Nonempty (DeepHornNeckConclusion Q.extension
                        (terminalAccuracyFactor * H'.epsilon) H'.constant rho delta horn h)



  scale_selection : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
    ∀ epsilon C analyticConstant : ℝ,
      0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → 0 < analyticConstant →
      ∀ A : RepairedNeckCapTopologyTheory.{u}, terminalAccuracyFactor * epsilon ≤ A.epsilon₀ →
        Nonempty (M32DeepHornScaleSelection.{u} epsilon C analyticConstant)



  selection : ∀ L31 : RepairedSingularRegularLimitTheory.{u},
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M]
      {F : GeneralizedRicciFlowData.{u}} {T : ℝ},
      ∀ H : SingularTimeAssumptions F T M,
        ∀ (A : RepairedNeckCapTopologyTheory.{u}),
          H.epsilon ≤ Classical.choose (L31.limit A) →
          terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀ →
        Nonempty (RepairedHornSelectionData H)

end PoincareConjecture
