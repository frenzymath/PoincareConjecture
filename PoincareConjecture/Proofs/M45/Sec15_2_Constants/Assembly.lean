import PoincareConjecture.Proofs.M45.Sec15_2_Constants.ProducerEndpoints
import PoincareConjecture.Proofs.M45.Sec15_2_Constants.ServiceExtraction
import PoincareConjecture.Proofs.M45.Sec15_2_Constants.CommonThreshold
import PoincareConjecture.Proofs.M45.Sec15_2_Constants.ConstantSelection
import PoincareConjecture.Proofs.M45.Ch12_Standard.CanonicalConstants
import PoincareConjecture.Statements.M45ControlledSchedules









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M45




theorem exists_calibratedSetup
    (A : RepairedNeckCapTopologyTheory.{u})
    (h27 : RepairedKappaAlternativeTheory.{u})
    (h28 : RepairedBoundedDistanceTheory.{u})
    (h31 : RepairedSingularRegularLimitTheory.{u})
    (h32 : RepairedHornSelectionTheory.{u})
    (smallNecks : ∃ epsilon₁ : ℝ, 0 < epsilon₁ ∧ M45SmallNeckScaleBound.{u} epsilon₁)
    (gluing : NeckGluingProducer.{u})
    (initialFlow : InitialFlowProducer.{u})
    (initialCapture : InitialCaptureProducer.{u})
    (models : M45ModelAnalyticBounds.{u})
    (capRefinement : CapRefinementProducer)
    {g₀ : StandardInitialMetric} (P : RepairedCapPersistenceData.{u} g₀)
    (U : RepairedStandardCapUniquenessData g₀ P.standard_cap)
    {prescribed : ℝ} (hprescribed : 0 < prescribed) :
    ∃ (setup : SurgeryControlSetup P.metric_surgery.constants) (kappa Delta : ℝ),
      ∃ h_initial : setup.standard_initial = g₀,
        HEq setup.standard_flow P.standard_cap.flow ∧
        Nonempty (M45ScheduleCalibration P.metric_surgery.constants setup kappa Delta
          g₀ P h_initial rfl) ∧ 2 * setup.epsilon ≤ prescribed := by
  classical
  obtain ⟨epsilon₁, h₁, hsmallNecks⟩ := smallNecks
  obtain ⟨epsilonPrime, hPrime, hkappa⟩ := kappaServices h27
  obtain ⟨epsilon₁₀, h₁₀, h₁₀le, hbounded, hdense⟩ := boundedDistanceServices h28
  obtain ⟨common, hcommon, hcommonA, hcommonLe, hlimit, hselection⟩ :=
    commonThresholdServices h31 h32 A
  let K := P.metric_surgery.constants
  let D := P.standard_cap.initial_estimate.scalar_constant
  let V := P.standard_cap.initial_estimate.core_volume_constant
  have hD : 0 < D := P.standard_cap.initial_estimate.scalar_constant_pos
  have hV : 0 < V := P.standard_cap.initial_estimate.core_volume_constant_pos
  have hradius : 0 < (Real.sqrt D * (g₀.cylindrical_end.radius + 5))⁻¹ := by
    apply inv_pos.mpr
    exact mul_pos (Real.sqrt_pos.mpr hD) (by linarith [g₀.cylindrical_end.radius_pos])
  obtain ⟨epsilon, hepsilon, hhalf, hsource, hsetupEpsilon, htwoBounded,
    htwoCommon, htwoPrescribed, htwoPrime, _⟩ :=
    exists_calibration_epsilon epsilon₁ epsilonPrime epsilon₁₀ common K.delta₀
      (Real.sqrt D * (g₀.cylindrical_end.radius + 5))⁻¹ prescribed
      h₁ hPrime h₁₀ hcommon K.delta₀_pos hradius hprescribed
  have hepsilonLe : epsilon ≤ 1 / 200 := hsetupEpsilon.trans (min_le_left _ _)
  obtain ⟨beta, hbeta, hbetaHalf, hgluing⟩ := gluing epsilon hepsilon hepsilonLe
  obtain ⟨hgamma, hgammaLe, hgammaHalf⟩ := comparison_accuracy hepsilon hepsilonLe hbeta hbetaHalf
  obtain ⟨Ckappa, hCkappa, hcanonical, hderivatives⟩ := hkappa epsilon hepsilon htwoPrime
  obtain ⟨Cstandard, hCstandard, hCstandardOne, hCstandardLocal, hstandard⟩ :=
    standardCanonicalServices U (beta * epsilon / 3) K.C₀ hgamma hgammaHalf
  let C := max Ckappa (Cstandard + 1)
  have hC : 0 < C := hCkappa.trans_le (le_max_left _ _)
  have hCle : Cstandard + 1 ≤ C := le_max_right _ _
  have hecommon : epsilon ≤ common := by linarith
  have hselectors (a : ℝ) (ha : 0 < a) :
      Nonempty (M32DeepHornScaleSelection.{u} epsilon C a) :=
    hselection epsilon C a hepsilon hecommon hC ha
  obtain ⟨H⟩ := hselectors 1 (by norm_num)
  have hheight : 0 < K.R₀ ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos K.R₀_pos _
  let selector := H.restrictHeight K.delta₀ (K.R₀ ^ (-1 / 2 : ℝ)) K.delta₀_pos hheight
  let setup : SurgeryControlSetup K :=
    { standard_initial := g₀
      standard_flow := P.standard_cap.flow
      standard_lifetime_one := U.lifetime_one
      epsilon := epsilon
      C := C
      epsilon_pos := hepsilon
      epsilon_lt_half := hhalf
      epsilon_le := hsetupEpsilon
      C_pos := hC
      C_large := by linarith
      C_ge_local := by linarith
      selector := selector.toCommonSurgeryScaleSelector
      selector_delta := fun rho delta _ _ =>
        H.restrictHeight_le_radius K.delta₀ _ K.delta₀_pos hheight rho delta }
  obtain ⟨kappa, hkappaPos, hflow⟩ := initialFlow epsilon hepsilon hepsilonLe
  let Delta := min (beta * epsilon / 3) (min K.delta₀ (min V⁻¹ D⁻¹))
  have calibration : M45ScheduleCalibration K setup kappa Delta g₀ P rfl rfl :=
    { epsilon₁ := epsilon₁
      epsilonPrime := epsilonPrime
      epsilon₁₀ := epsilon₁₀
      epsilon₁_pos := h₁
      small_neck_scale_bound := hsmallNecks
      epsilonPrime_pos := hPrime
      epsilon₁₀_pos := h₁₀
      epsilon₁₀_le := h₁₀le
      two_epsilon_le_bounded_distance := htwoBounded
      bounded_distance := hbounded
      bounded_distance_dense := hdense
      appendixA := A
      common_epsilon := common
      common_epsilon_pos := hcommon
      terminal_common_epsilon_le_appendixA := hcommonA
      two_common_epsilon_le := hcommonLe
      two_epsilon_le_common := htwoCommon
      singular_limit := hlimit
      epsilon_source_le := hsource
      beta := beta
      beta_pos := hbeta
      beta_lt_half := hbetaHalf
      gluing := hgluing
      Ckappa := Ckappa
      Cstandard := Cstandard
      Ckappa_pos := hCkappa
      Cstandard_pos := hCstandard
      setup_C_eq := rfl
      model_analytics := models
      kappa_canonical := hcanonical
      kappa_derivatives := hderivatives
      canonical_source := hstandard
      cap_refinement := fun _ _ N => capRefinement hgammaLe N
      kappa₀_pos := hkappaPos
      claim151 := hflow
      initial_capture := initialCapture epsilon kappa hepsilon hepsilonLe hkappaPos hflow
      delta₁₃ := K.delta₀
      delta₁₃_pos := K.delta₀_pos
      delta₁₃_le := le_rfl
      delta_zero_eq := rfl
      analytic_constant := 1
      analytic_constant_pos := by norm_num
      horn_selection := hselectors
      horn_selector := selector
      selector_eq := rfl
      selector_initial_bound :=
        H.restrictHeight_le_bound K.delta₀ _ K.delta₀_pos hheight _ _ }
  exact ⟨setup, kappa, Delta, rfl, HEq.rfl, ⟨calibration⟩, htwoPrescribed⟩




theorem controlledSchedulesOfProducers
    (A : RepairedNeckCapTopologyTheory.{u})
    (h27 : RepairedKappaAlternativeTheory.{u})
    (h28 : RepairedBoundedDistanceTheory.{u})
    (h31 : RepairedSingularRegularLimitTheory.{u})
    (h32 : RepairedHornSelectionTheory.{u})
    (smallNecks : ∃ epsilon₁ : ℝ, 0 < epsilon₁ ∧ M45SmallNeckScaleBound.{u} epsilon₁)
    (gluing : NeckGluingProducer.{u})
    (initialFlow : InitialFlowProducer.{u})
    (initialCapture : InitialCaptureProducer.{u})
    (models : M45ModelAnalyticBounds.{u})
    (capRefinement : CapRefinementProducer) : RepairedControlledSchedulesTheory.{u} := by
  refine ⟨?_⟩
  intro h34 h35 h36 h44 prescribed hprescribed
  obtain ⟨g₀⟩ := h34.initial_metric
  obtain ⟨P⟩ := h44.persistence h34 h35 h36 g₀
  obtain ⟨U⟩ := P.standard_cap_uniqueness
  obtain ⟨setup, kappa, Delta, h_initial, h_flow, ⟨calibration⟩, hbound⟩ :=
    exists_calibratedSetup A h27 h28 h31 h32 smallNecks gluing initialFlow
      initialCapture models capRefinement P U hprescribed
  refine ⟨{
    constants := P.metric_surgery.constants
    setup := setup
    kappa0 := kappa
    Delta0 := Delta
    standard_initial := g₀
    setup_standard_initial_eq := h_initial
    cap_persistence := P
    cap_constants_eq := rfl
    setup_standard_flow_eq := h_flow
    calibration := calibration }, hbound⟩

end PoincareConjecture.M45
