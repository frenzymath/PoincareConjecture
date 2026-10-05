import PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornSelection
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Classification
import PoincareLib.Topology.Manifold.NeckCap.Theory
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.BoundsTheory
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.LimitTheory

/-!
Adapted from Mapher `PoincareMT/Statements/M32HornSelection.lean` at
`0bf00434d6783c9fed79b6a8fa3a8349cfc78335`. Declaration bodies are retained;
see `references/ricci-flow/mapher/terminal-accuracy-contract.json`.
-/

/-!
# M32 repaired strong-neck and deep-horn selection statement

The horn-selection output is quantified over each generalized flow and finite
singular terminal time satisfying the repaired assumptions. Its provider
boundary exposes M04 curvature calculus and evolution, the M19 round-sphere
classification, the M29 bounded-distance
service, and the M30 compactness service used by the source argument; an
explicit M25 Appendix A neck/cap theory and small-epsilon inequality are passed
when the selection is applied. The monotone selector includes the actual
deep-horn conclusion at every smaller positive height. Both its threshold
and M31's threshold are uniform across reference manifolds.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! Source services used in the contradiction argument for Theorem 11.31. -/
structure RepairedHornSelectionPredecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  m19_round : ∀ {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
    [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
    [T2Space N] [T3Space N] [SecondCountableTopology N]
    [ConnectedSpace N],
    ∀ K : AncientKappaSolution 2 N,
      Nonempty (TwoDimensionalAncientRoundCertificate K)
  m29 : DenseGeneralizedBoundedDistanceTheory.{u}
  m30 : RepairedControlledBlowupLimitTheory.{u}

structure RepairedHornSelectionTheory : Prop where
  /-- Compatibility metadata; the geometric conclusions are the fields below. -/
  providers : RepairedHornSelectionPredecessors.{u}
  /-- Theorem 11.31 with a common M29/M30 threshold selected before epsilon,
  then h selected before any flow, terminal limit, or input horn is quantified. -/
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
  /-- Corollary 11.36 with a common two-variable selector. The radius-change
  argument retains each supplied terminal extension, and the geometric
  conclusion is valid at every smaller positive height. -/
  scale_selection : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
    ∀ epsilon C analyticConstant : ℝ,
      0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → 0 < analyticConstant →
      ∀ A : RepairedNeckCapTopologyTheory.{u},
        terminalAccuracyFactor * epsilon ≤ A.epsilon₀ →
        Nonempty (M32DeepHornScaleSelection.{u} epsilon C analyticConstant)
  /-- Compatibility-only repackaging of M31. Its independently chosen limit
  is not asserted to equal another M31 choice. Actual surgery applies
  `deep_horn` or `scale_selection` to its already selected limit. -/
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

end PoincareMT
