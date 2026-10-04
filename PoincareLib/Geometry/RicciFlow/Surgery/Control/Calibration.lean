import PoincareLib.Geometry.RicciFlow.Surgery.Control.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceData
import PoincareLib.Geometry.RicciFlow.Surgery.Control.NeckGluing
import PoincareLib.Geometry.RicciFlow.Surgery.Control.SmallNecks
import PoincareLib.Geometry.RicciFlow.Surgery.Control.CapRefinement
import PoincareLib.Geometry.RicciFlow.Surgery.Control.ModelBounds
import PoincareLib.Geometry.RicciFlow.Surgery.Control.InitialControl
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Alternatives
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Limit
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornSelection
import PoincareLib.Topology.Manifold.NeckCap.Theory

/-!
Adapted from Mapher `PoincareMT/Definitions/M45ControlledSchedules.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M45 calibrated surgery setup and initial seeds

The fixed setup and Definition 15.7's initial seeds precede the inductive
choice of finite parameter sequences. M46/M47 apply to each compatible
finite prefix; M48 constructs an extension with their selected constants.
Only M51 constructs the global schedule. This boundary does not claim that
the remaining geometric calibration and analytic producers are available.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! The source-calibration interface is kept local to M45.  The generic
    Chapter 16/17 schedule records retain their numerical scaffolding for
    compatibility, while this record names the primitive values that later
    proof work must obtain from Morgan--Tian's cited results. -/
structure M45ScheduleCalibration
    (K : MetricSurgeryConstants)
    (setup : SurgeryControlSetup K) (kappa0 Delta0 : ℝ)
    (g₀ : StandardInitialMetric)
    (P : RepairedCapPersistenceData.{u} g₀)
    (h_initial : setup.standard_initial = g₀)
    (h_constants : P.metric_surgery.constants = K) where
  /-- Proposition 2.19, Theorem 9.93, and Chapter 10 threshold values. -/
  epsilon₁ : ℝ
  epsilonPrime : ℝ
  epsilon₁₀ : ℝ
  epsilon₁_pos : 0 < epsilon₁
  small_neck_scale_bound : M45SmallNeckScaleBound.{u} epsilon₁
  epsilonPrime_pos : 0 < epsilonPrime
  epsilon₁₀_pos : 0 < epsilon₁₀
  epsilon₁₀_le : epsilon₁₀ ≤ 1 / 200
  two_epsilon_le_bounded_distance : 2 * setup.epsilon ≤ epsilon₁₀
  /-- Theorem 10.2 retains one threshold before every canonical constant.
      Claim 17.9 applies it at twice the setup constant and accuracy. -/
  bounded_distance :
    ∀ eta : ℝ, 0 < eta → eta ≤ epsilon₁₀ →
      ∀ C' : ℝ, 0 < C' → ∀ a : ℝ, 0 ≤ a →
        ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
          ∀ F : GeneralizedRicciFlowData.{u},
            F.interval ⊆ Set.Ici 0 → generalizedHamiltonIveyPinched F →
            ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
              D₀ ≤ F.scalar ⟨t, x⟩ →
              generalizedEarlierStrongCanonicalNeighborhoods F eta C' t x →
              RepairedBoundedDistanceEstimate F a D t x
  /-- The same threshold also controls histories whose whole canonical
      slices are left-dense, including the retained history at old events. -/
  bounded_distance_dense : M28DenseTimeEstimateStatement.{u} epsilon₁₀
  /-- The actual Appendix A service and its common M31/M32 threshold are
      retained together before the reference manifold is chosen. -/
  appendixA : RepairedNeckCapTopologyTheory.{u}
  common_epsilon : ℝ
  common_epsilon_pos : 0 < common_epsilon
  two_common_epsilon_le_appendixA :
    terminalAccuracyFactor * common_epsilon ≤ appendixA.epsilon₀
  two_common_epsilon_le : 2 * common_epsilon ≤ 1 / 200
  two_epsilon_le_common : 2 * setup.epsilon ≤ common_epsilon
  singular_limit :
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M]
      {F : GeneralizedRicciFlowData.{u}} {T : ℝ},
      ∀ H : SingularTimeAssumptions F T M,
        H.epsilon ≤ common_epsilon → Nonempty (RepairedSingularRegularLimitData H)
  /-- The exact minimum used in the first-assumptions paragraph of Chapter 15. -/
  epsilon_source_le :
    setup.epsilon ≤
      min (1 / 200 : ℝ)
        (min ((Real.sqrt P.standard_cap.initial_estimate.scalar_constant *
          (g₀.cylindrical_end.radius + 5))⁻¹)
          (min (epsilon₁ / 2) (min (epsilonPrime / 2) epsilon₁₀)))
  /-- Proposition 15.2 at this fixed epsilon, with the actual two-flow
      gluing property. The stronger universal-beta source claim is separate. -/
  beta : ℝ
  beta_pos : 0 < beta
  beta_lt_half : beta < 1 / 2
  gluing : M45NeckGluingProperty.{u} setup.epsilon beta
  /-- Corollary 9.94 and Theorem 12.32 constants, with the source +1 margin. -/
  Ckappa : ℝ
  Cstandard : ℝ
  Ckappa_pos : 0 < Ckappa
  Cstandard_pos : 0 < Cstandard
  setup_C_eq : setup.C = max Ckappa (Cstandard + 1)
  /-- Intrinsic four-jet estimates are outputs of this calibration, with
      constants independent of its selected surgery height. -/
  model_analytics : M45ModelAnalyticBounds.{u}
  /-- Corollary 9.94 retains its projective-plane exception at both accuracies. -/
  kappa_canonical :
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
      ∀ K : AncientKappaSolution 3 M,
        ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) →
        ∀ eta : ℝ, (eta = setup.epsilon ∨ eta = 2 * setup.epsilon) →
          ∀ t, t ≤ 0 → ∀ x : M, M27StrongCanonicalNeighborhood K t x eta Ckappa
  /-- Theorem 9.93's derivative estimate has no projective-plane exception
      and no epsilon parameter. -/
  kappa_derivatives :
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
      ∀ K : AncientKappaSolution 3 M, M27ScalarDerivativeBounds K Ckappa
  canonical_source :
    ∀ t ∈ Set.Ico 0 P.standard_cap.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        StandardCanonicalAlternative P.standard_cap.atlas P.standard_cap.flow t x
          (beta * setup.epsilon / 3) Cstandard
  /-- Definition 9.72 and Remark 9.73, pp. 230--231. The uniform +1 margin
      and the core-facing end orientation are constructed, not assumed. -/
  cap_refinement : ∀ t : ℝ, ∀ x : StandardCapSpace,
    ∀ N : StandardCapNeighborhood P.standard_cap.atlas P.standard_cap.flow t
      (beta * setup.epsilon / 3) Cstandard x,
      Nonempty (M45StandardCapRefinement N)
  /-- Claim 15.1's universal initial-flow and noncollapsing seed. -/
  kappa₀_pos : 0 < kappa0
  claim151 :
    ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M]
      [BorelSpace M] [T2Space M] [T3Space M]
      [CompactSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [SecondCountableTopology M],
      ∀ N : NormalizedInitialMetric (M := M),
        ∃ F : RicciFlow 3 M (Set.Icc 0 (1 / 16 : ℝ)),
          F.metric 0 = N.metric ∧
          HEq (F.connection 0) N.connection ∧
          (∀ t ∈ Set.Icc 0 (1 / 16 : ℝ), ∀ x : M,
            (F.connection t).curvatureTensorNorm x ≤ 2) ∧
          (∀ t ∈ Set.Icc 0 (1 / 16 : ℝ), ∀ x : M, ∀ r : ℝ,
            0 < r → r ≤ setup.epsilon →
              ENNReal.ofReal (kappa0 * r ^ 3) ≤
                calibratedMetricVolume (F.metric t) ((F.metric t).ball x r))
  /-- Claim 15.1 on the supplied raw flow, using ordinary uniqueness and
      the no-early-surgery maximality argument of p. 360. -/
  initial_capture : M45InitialSurgeryControl.{u} setup.epsilon kappa0
  /-- Theorem 13.2's cutoff and the two Lemma 12.3 initial estimates. -/
  delta₁₃ : ℝ
  delta₁₃_pos : 0 < delta₁₃
  delta₁₃_le : delta₁₃ ≤ K.delta₀
  delta_zero_eq :
    Delta0 = min (beta * setup.epsilon / 3)
      (min delta₁₃
        (min P.standard_cap.initial_estimate.core_volume_constant⁻¹
          P.standard_cap.initial_estimate.scalar_constant⁻¹))
  /-- The active coefficient indexes the height choice. This numerical
      record alone cannot instantiate M48: its separate calibration retains
      the actual M47 component estimate and the required domination bounds. -/
  analytic_constant : ℝ
  analytic_constant_pos : 0 < analytic_constant
  /-- M32 permits reselection after the analytic coefficient is fixed,
      before choosing prefixes or flows. -/
  horn_selection : ∀ A : ℝ, 0 < A →
    Nonempty (M32DeepHornScaleSelection.{u} setup.epsilon setup.C A)
  /-- The selected and restricted M32 geometric height, at the final C and
      analytic coefficient, acts on each supplied terminal limit. -/
  horn_selector :
    M32DeepHornScaleSelection.{u} setup.epsilon setup.C analytic_constant
  selector_eq : setup.selector = horn_selector.toCommonSurgeryScaleSelector
  selector_initial_bound :
    setup.selector.h (Delta0 * setup.epsilon) Delta0 ≤
      K.R₀ ^ (-1 / 2 : ℝ)

structure RepairedControlledSchedulesData where
  constants : MetricSurgeryConstants
  setup : SurgeryControlSetup constants
  kappa0 : ℝ
  Delta0 : ℝ
  /-- The selected standard-cap and surgery objects used to calibrate the
      setup are retained as actual values, rather than represented only by
      unconstrained numerical fields. -/
  standard_initial : StandardInitialMetric
  setup_standard_initial_eq : setup.standard_initial = standard_initial
  cap_persistence : RepairedCapPersistenceData.{u} standard_initial
  cap_constants_eq : cap_persistence.metric_surgery.constants = constants
  setup_standard_flow_eq : HEq setup.standard_flow
    cap_persistence.standard_cap.flow
  /-- Source-facing calibration values and applied primitive estimates. -/
  calibration :
    M45ScheduleCalibration.{u} constants setup kappa0 Delta0 standard_initial
      cap_persistence setup_standard_initial_eq cap_constants_eq

/-- Definition 15.7's fixed initial entries. All remaining prefix entries
are primitive positive antitone data, not restrictions of a future schedule. -/
structure RepairedControlledSchedulesData.SeedCompatible
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) : Prop where
  setup_eq : p.setup = S.setup
  kappa_zero_eq : p.kappa 0 = S.kappa0
  Delta_zero_eq : p.Delta 0 = S.Delta0

end PoincareMT
