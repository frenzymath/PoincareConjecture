import PoincareConjecture.Definitions.Ch16.ControlledSurgery
import PoincareConjecture.Definitions.M44CapPersistence
import PoincareConjecture.Definitions.M45NeckGluing
import PoincareConjecture.Definitions.M45SmallNecks
import PoincareConjecture.Definitions.M45StandardGeometry
import PoincareConjecture.Definitions.M45ModelAnalytics
import PoincareConjecture.Definitions.M45InitialControl
import PoincareConjecture.Definitions.M27KappaAlternatives
import PoincareConjecture.Statements.M28BoundedDistance
import PoincareConjecture.Definitions.M31SingularRegularLimit
import PoincareConjecture.Definitions.M32HornSelection
import PoincareConjecture.Statements.M25NeckCapTopology











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture





structure M45ScheduleCalibration
    (K : MetricSurgeryConstants)
    (setup : SurgeryControlSetup K) (kappa0 Delta0 : ℝ)
    (g₀ : StandardInitialMetric)
    (P : RepairedCapPersistenceData.{u} g₀)
    (h_initial : setup.standard_initial = g₀)
    (h_constants : P.metric_surgery.constants = K) where

  epsilon₁ : ℝ
  epsilonPrime : ℝ
  epsilon₁₀ : ℝ
  epsilon₁_pos : 0 < epsilon₁
  small_neck_scale_bound : M45SmallNeckScaleBound.{u} epsilon₁
  epsilonPrime_pos : 0 < epsilonPrime
  epsilon₁₀_pos : 0 < epsilon₁₀
  epsilon₁₀_le : epsilon₁₀ ≤ 1 / 200
  two_epsilon_le_bounded_distance : 2 * setup.epsilon ≤ epsilon₁₀


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


  bounded_distance_dense : M28DenseTimeEstimateStatement.{u} epsilon₁₀




  appendixA : RepairedNeckCapTopologyTheory.{u}
  common_epsilon : ℝ
  common_epsilon_pos : 0 < common_epsilon
  terminal_common_epsilon_le_appendixA :
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

  epsilon_source_le :
    setup.epsilon ≤
      min (1 / 200 : ℝ)
        (min ((Real.sqrt P.standard_cap.initial_estimate.scalar_constant *
          (g₀.cylindrical_end.radius + 5))⁻¹)
          (min (epsilon₁ / 2) (min (epsilonPrime / 2) epsilon₁₀)))


  beta : ℝ
  beta_pos : 0 < beta
  beta_lt_half : beta < 1 / 2
  gluing : M45NeckGluingProperty.{u} setup.epsilon beta

  Ckappa : ℝ
  Cstandard : ℝ
  Ckappa_pos : 0 < Ckappa
  Cstandard_pos : 0 < Cstandard
  setup_C_eq : setup.C = max Ckappa (Cstandard + 1)


  model_analytics : M45ModelAnalyticBounds.{u}

  kappa_canonical :
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
      ∀ K : AncientKappaSolution 3 M,
        ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) →
        ∀ eta : ℝ, (eta = setup.epsilon ∨ eta = 2 * setup.epsilon) →
          ∀ t, t ≤ 0 → ∀ x : M, M27StrongCanonicalNeighborhood K t x eta Ckappa


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


  cap_refinement : ∀ t : ℝ, ∀ x : StandardCapSpace,
    ∀ N : StandardCapNeighborhood P.standard_cap.atlas P.standard_cap.flow t
      (beta * setup.epsilon / 3) Cstandard x,
      Nonempty (M45StandardCapRefinement N)

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


  initial_capture : M45InitialSurgeryControl.{u} setup.epsilon kappa0

  delta₁₃ : ℝ
  delta₁₃_pos : 0 < delta₁₃
  delta₁₃_le : delta₁₃ ≤ K.delta₀
  delta_zero_eq :
    Delta0 = min (beta * setup.epsilon / 3)
      (min delta₁₃
        (min P.standard_cap.initial_estimate.core_volume_constant⁻¹
          P.standard_cap.initial_estimate.scalar_constant⁻¹))



  analytic_constant : ℝ
  analytic_constant_pos : 0 < analytic_constant


  horn_selection : ∀ A : ℝ, 0 < A →
    Nonempty (M32DeepHornScaleSelection.{u} setup.epsilon setup.C A)


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



  standard_initial : StandardInitialMetric
  setup_standard_initial_eq : setup.standard_initial = standard_initial
  cap_persistence : RepairedCapPersistenceData.{u} standard_initial
  cap_constants_eq : cap_persistence.metric_surgery.constants = constants
  setup_standard_flow_eq : HEq setup.standard_flow
    cap_persistence.standard_cap.flow

  calibration :
    M45ScheduleCalibration.{u} constants setup kappa0 Delta0 standard_initial
      cap_persistence setup_standard_initial_eq cap_constants_eq



structure RepairedControlledSchedulesData.SeedCompatible
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) : Prop where
  setup_eq : p.setup = S.setup
  kappa_zero_eq : p.kappa 0 = S.kappa0
  Delta_zero_eq : p.Delta 0 = S.Delta0

end PoincareConjecture
