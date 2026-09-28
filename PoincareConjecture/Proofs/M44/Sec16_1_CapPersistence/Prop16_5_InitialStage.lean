import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_ControlledStages
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialSampleBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalInitialSurvival

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance initialStageCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialStageCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

theorem CapPersistenceCounterexample.fixed_scales_of_cutoff_le
    {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
    {start rNext A eta theta cutoff delta : ℝ}
    (X : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff)
    (h : cutoff ≤ delta) :
    SurgeryFixedScalesOn setup X.flow X.observation start rNext delta :=
  { X.fixed_scales with delta_le := fun t ht => (X.fixed_scales.delta_le t ht).trans h }

theorem exists_initial_cap_sequence_stage
    (P : M44CapPersistencePredecessors.{u})
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    {rNext Rinner : ℝ} (hr : 0 < rNext) (hinner : 0 < Rinner) :
    ∃ R0 tau K : ℝ, Rinner < R0 ∧ 2 < R0 ∧ 0 < tau ∧ 0 < K ∧
      ∀ start A eta theta : ℝ, ∀ {cutoffs : ℕ → ℝ},
      ∀ X : ∀ n, PreparedCapCounterexample.{u}
        setup start rNext A eta theta (cutoffs n) Rinner,
      Tendsto cutoffs atTop (𝓝 0) →
      Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0) →
        CapSequenceStage X R0 tau K := by
  obtain ⟨RS, tauS, hinnerS, hRS, htauS, hsurvival⟩ :=
    exists_initial_outer_survival_cutoff P standard constants
      setup.epsilon_pos setup.C_pos hr hinner
  obtain ⟨x, u, v, _hcompact, hcollar⟩ :=
    exists_global_standard_collar standard setup.C_pos (theta := 0) le_rfl zero_lt_one
  have hJ := hcollar 0 ⟨le_rfl, le_rfl⟩
  change metricTwoJet (standard.flow.base.flow.metric 0).euclideanCoefficients x ∈
    collarJetRegion setup.C u v at hJ
  rw [standard.flow.base.initial_metric] at hJ
  let R0 := |M36.radialArclength setup.standard_initial ‖x‖| + RS + 4
  have hSR0 : RS ≤ R0 := by
    dsimp [R0]
    linarith only [abs_nonneg (M36.radialArclength setup.standard_initial ‖x‖)]
  have hR0 : 2 < R0 := hRS.trans_le hSR0
  have hx : x ∈ setup.standard_initial.metric.ball 0 (R0 - 2) := by
    change setup.standard_initial.metric.edist 0 x < ENNReal.ofReal (R0 - 2)
    rw [M36.standard_edist_zero,
      ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R0 - 2)]
    dsimp only [R0]
    linarith only [le_abs_self (M36.radialArclength setup.standard_initial ‖x‖), hRS]
  obtain ⟨dI, tauI, K, hdI, htauI, hK, hinitial⟩ :=
    exists_initial_sample_bound P setup.standard_initial standard.initial_estimate
      setup.C x u v hJ hR0 hx
  obtain ⟨dh, hdh, hheight⟩ := exists_surgery_normalization_cutoff setup.epsilon_pos hr
  refine ⟨R0, min tauS tauI, K, hinnerS.trans_le hSR0, hR0,
    lt_min htauS htauI, hK, ?_⟩
  intro start A eta theta cutoffs X hcutoffs heta R hR
  have hRpos : 0 < R := (by linarith : 0 < R0).trans_le hR
  obtain ⟨dS, hdS, hsurvive⟩ := hsurvival R (hSR0.trans hR)
  have hfitCutoff : 0 < 1 / (R + 1) := by positivity
  filter_upwards [hcutoffs.eventually (gt_mem_nhds hdS),
    hcutoffs.eventually (gt_mem_nhds hdh), heta.eventually (gt_mem_nhds hdI),
    heta.eventually (gt_mem_nhds hfitCutoff)] with n hcutS hcutH hetaI hetaFit
  have hfit : R < (X n).sample.eta⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ (X n).sample.comparison.eta_pos]
    have hmul := (lt_div_iff₀ (by positivity : 0 < R + 1)).mp hetaFit
    nlinarith [(X n).sample.comparison.eta_pos]
  have htime (s : ℝ) (hs : s ∈ Ico 0 (X n).data.assignedDuration) :
      (X n).data.time + s / (((X n).data.flow.parameters.h (X n).data.time)⁻¹ ^ 2) ∈
        (X n).data.flow.time_domain :=
    (X n).data.observation.interval_subset ((X n).data.assigned_time_mem hs).1
  obtain ⟨D, hDR, hDeta, hDmap⟩ := exists_maximal_cap_sample P
    (X n).data.flow (X n).data.time (X n).data.is_surgery (X n).data.cap
    (X n).data.fixed_scales.standard_initial_eq (X n).data.pinched
    ((X n).sample.lifetime_pos.trans_le (X n).sample.lifetime_le)
    hRpos hfit htime (X n).sample.comparison (X n).sample.image_ball
  have hscales := (X n).data.fixed_scales_of_cutoff_le hcutS.le
  have hsurviveD := hsurvive (X n).data.flow
    (X n).data.fixed_scales.standard_initial_eq (X n).data.fixed_scales.local_constants_eq
    (X n).data.fixed_scales.epsilon_eq (X n).data.fixed_scales.C_eq
    (X n).data.observation setup hscales (X n).data.time (X n).data.is_surgery
    ((X n).data.birth_delta_le.trans hcutS.le) (X n).data.cap
    (X n).data.assignedDuration D.lifetime (X n).sample.lifetime
    D.lifetime_pos (X n).sample.lifetime_le
    (fun _ hs => (X n).data.assigned_time_mem hs) (X n).data.canonical (X n).data.pinched
  rw [← hDR, ← D.region_eq] at hsurviveD
  have hinnerRadius : (X n).sample.radius ≤ D.radius := by
    rw [(X n).radius_eq, hDR]
    exact (hinnerS.trans_le hSR0).le.trans hR
  have hsurv : min (X n).sample.lifetime tauS ≤ D.lifetime :=
    hsurviveD D.cylinder D.birth_identity D.maximal
      ((X n).sample.region_subset_of_radius_le D hinnerRadius)
      (X n).sample.region_nonempty (X n).sample.cylinder (X n).sample.birth_identity
  have hstageSurv : min (X n).sample.lifetime (min tauS tauI) ≤ D.lifetime :=
    (min_le_min_left _ (min_le_left tauS tauI)).trans hsurv
  have hbirth0 := (X n).data.flow.time_domain_nonnegative
    ((X n).data.flow.surgery_times_subset (X n).data.is_surgery)
  obtain ⟨hsmall, hthreshold⟩ := hheight (X n).data.flow.parameters
    (X n).data.fixed_scales.epsilon_eq (X n).data.time hbirth0
    ((X n).data.birth_delta_le.trans hcutH.le)
  have hq : (X n).data.flow.parameters.h (X n).data.time ^ 2 * (rNext⁻¹ ^ 2) ≤ 1 := by
    simpa only [div_pow, div_eq_mul_inv, mul_pow, inv_pow] using hthreshold
  have hcanonical (s : ℝ) (hs : s ∈ Ico (0 : ℝ) D.lifetime)
      (y : ((X n).data.flow.slice ((X n).data.time +
        s / (((X n).data.flow.parameters.h (X n).data.time)⁻¹ ^ 2))).carrier)
      (hy : rNext⁻¹ ^ 2 ≤ ((X n).data.flow.connection ((X n).data.time +
        s / (((X n).data.flow.parameters.h (X n).data.time)⁻¹ ^ 2))).scalarCurvature y) :
      SurgeryCanonicalControl (X n).data.flow ((X n).data.time +
        s / (((X n).data.flow.parameters.h (X n).data.time)⁻¹ ^ 2)) y
        (X n).data.flow.parameters.epsilon setup.C := by
    rw [← (X n).data.fixed_scales.C_eq]
    exact (X n).data.canonical _
      ((X n).data.assigned_time_mem ⟨hs.1, hs.2.trans_le D.lifetime_le⟩).1
      (D.cylinder.time_subset (mem_image_of_mem _ hs)) y hy
  have hbound := hinitial (X n).data.flow (X n).data.time (X n).data.is_surgery
    (X n).data.cap D.toCylinderCompactnessSample (by simpa only [hDR] using hR)
    (by simpa only [hDeta] using hetaI.le) D.region_open hsmall
    (rNext⁻¹ ^ 2) hq hcanonical (X n).data.pinched
  refine ⟨⟨D, hDR, hDeta, hDmap, hstageSurv, ?_⟩⟩
  intro t ht y
  apply hbound t ⟨ht.1, lt_min (ht.2.trans_le hstageSurv) ?_⟩ y
  exact ht.2.trans_le ((min_le_right (X n).sample.lifetime (min tauS tauI)).trans
    (min_le_right tauS tauI))

end PoincareConjecture.M44
