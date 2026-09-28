import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_StageComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalRestartControl
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_ScalarComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_SmallHeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance restartStageCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance restartStageCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

theorem exists_cap_sequence_restart
    (P : M44CapPersistencePredecessors.{u})
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    {rNext Rinner theta Ki : ℝ} (hr : 0 < rNext) (hinner : 0 < Rinner)
    (htheta : 0 < theta) (htheta1 : theta < 1) (hKi : 0 < Ki) :
    ∃ R1 increment K : ℝ, Rinner < R1 ∧ 2 < R1 ∧ 0 < increment ∧ 0 < K ∧ Ki ≤ K ∧
      ∀ start A eta : ℝ, ∀ {cutoffs : ℕ → ℝ},
      ∀ X : ∀ n, PreparedCapCounterexample.{u}
        setup start rNext A eta theta (cutoffs n) Rinner,
      Tendsto cutoffs atTop (𝓝 0) →
      Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0) →
      ∀ c : ℝ, 0 ≤ c → c ≤ theta →
      Tendsto (fun n => (X n).sample.lifetime) atTop (𝓝 c) →
      ∀ R0 T : ℝ, R1 ≤ R0 → 0 < T → T ≤ c →
      CapSequenceStage X R0 T K → CapSequenceStage X R0 (T + increment) K := by
  obtain ⟨M0, hM0, hmodel⟩ :=
    exists_global_standard_scalar_bound standard htheta.le htheta1
  let M := M0 + 1
  have hM : 0 < M := by dsimp [M]; linarith
  have hOneM : 1 ≤ M := by dsimp [M]; linarith
  let K := max Ki (13 * max (2 * M) (Real.exp 4))
  have hK : 0 < K := hKi.trans_le (le_max_left _ _)
  have hnewK : 13 * max (2 * M) (Real.exp 4) ≤ K := le_max_right _ _
  obtain ⟨R1, tau, accuracy, compact, hinnerR1, hR1, htau, haccuracy,
    hcompact, hinside, hrestart⟩ :=
    exists_restarted_outer_control_cutoff P standard setup.C_pos hinner
      htheta htheta1 hM (r := rNext) (Kpast := K)
  obtain ⟨dh, hdh, hheight⟩ := exists_surgery_normalization_cutoff setup.epsilon_pos hr
  refine ⟨R1, tau / 2, K, hinnerR1, hR1, half_pos htau, hK, le_max_left _ _, ?_⟩
  intro start A eta cutoffs X hcutoffs heta c hc hctheta hlim R0 T hR10 hT hTc hstage
  let a := max 0 (T - tau / 2)
  have ha : 0 ≤ a := le_max_left _ _
  have haT : a < T := max_lt hT (sub_lt_self T (half_pos htau))
  have hac : a < c := haT.trans_le hTc
  have haTheta : a ∈ Icc (0 : ℝ) theta := ⟨ha, hac.le.trans hctheta⟩
  have hnext : T + tau / 2 ≤ a + tau := by
    have h := le_max_right (0 : ℝ) (T - tau / 2)
    dsimp only [a]
    linarith
  have hnear := eventually_stage_twoJet_comparison P standard unique hstage heta hlim
    hT hK htheta htheta1 hc hctheta hcompact haccuracy
  intro R hR
  have hRpos : 0 < R := (by linarith : 0 < R1).trans_le (hR10.trans hR)
  obtain ⟨eta0, delta0, heta0, hdelta0, hcontrol⟩ := hrestart R (hR10.trans hR)
  let closedBall := {x : E | setup.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal R}
  have hclosed : IsCompact closedBall :=
    M36.standard_closed_ball_compact setup.standard_initial hRpos.le
  obtain ⟨scalarAccuracy, hscalarAccuracy, hscalarMargin⟩ :=
    exists_standard_scalar_comparison_tolerance standard htheta1 hmodel hclosed
  have hscalarNear := eventually_stage_twoJet_comparison P standard unique hstage heta hlim
    hT hK htheta htheta1 hc hctheta hclosed hscalarAccuracy
  filter_upwards [hstage R hR, hnear, hscalarNear,
    hcutoffs.eventually (gt_mem_nhds hdelta0), hcutoffs.eventually (gt_mem_nhds hdh),
    heta.eventually (gt_mem_nhds heta0), hlim.eventually (lt_mem_nhds hac)] with
    n hn hnearN hscalarNearN hdeltaN hheightN hetaN hlifeN
  obtain ⟨D⟩ := hn
  have haStage : a ∈ Ico (0 : ℝ) (min (X n).sample.lifetime T) :=
    ⟨ha, lt_min hlifeN haT⟩
  have haD : a < D.outer.lifetime := haStage.2.trans_le D.survival
  have hscalar : ∀ y, (D.outer.ordinary.flow.connection a).scalarCurvature y ≤ M := by
    apply D.outer.toCylinderCompactnessSample.scalar_le_of_source_twoJet_bound a
    intro x hx
    have hxClosed : x ∈ closedBall := by
      rw [D.outer.toCylinderCompactnessSample.source_eq, D.radius_eq] at hx
      change setup.standard_initial.metric.edist 0 x < ENNReal.ofReal R at hx
      change setup.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal R
      exact hx.le
    exact (hscalarMargin a haTheta x hxClosed _
      (hscalarNearN D.outer.toCylinderCompactnessSample D.comparison_eq
        a haStage haD x hxClosed hx)).le
  have hpast : ∀ s ∈ Icc (0 : ℝ) a, ∀ y,
      (D.outer.ordinary.flow.connection s).curvatureTensorNorm y ≤ K := by
    intro s hs y
    exact D.curvature s ⟨hs.1, hs.2.trans_lt haStage.2⟩ y
  have hnearD : ∀ x ∈ compact,
      ‖metricTwoJet (fun y => D.outer.toCylinderCompactnessSample.coefficients (a, y)) x -
        metricTwoJet (standard.flow.metric a).euclideanCoefficients x‖ ≤ accuracy := by
    intro x hx
    apply hnearN D.outer.toCylinderCompactnessSample D.comparison_eq a haStage haD x hx
    rw [D.outer.toCylinderCompactnessSample.source_eq, D.radius_eq]
    exact (hinside hx).trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨hsmall, hthreshold⟩ := hheight (X n).data.flow.parameters
    (X n).data.fixed_scales.epsilon_eq (X n).data.time (X n).data.observation_time.1
    ((X n).data.birth_delta_le.trans hheightN.le)
  have hq : (X n).data.flow.parameters.h (X n).data.time ^ 2 * (rNext⁻¹ ^ 2) ≤ M := by
    apply le_trans _ hOneM
    simpa only [div_pow, div_eq_mul_inv, mul_pow, inv_pow] using hthreshold
  have hinnerRadius : (X n).sample.radius ≤ D.outer.radius := by
    rw [(X n).radius_eq, D.radius_eq]
    exact hinnerR1.le.trans (hR10.trans hR)
  have hcontrolD := hcontrol (X n).data.flow (X n).data.observation setup
    (X n).data.fixed_scales hdeltaN.le (X n).data.time (X n).data.is_surgery (X n).data.cap
    (X n).data.assignedDuration_le (fun _ hs => (X n).data.assigned_time_mem hs)
    D.outer D.radius_eq (by simpa only [D.eta_eq] using hetaN.le) hsmall hq
    (X n).data.fixed_scales.C_eq (X n).data.canonical (X n).data.pinched
    a ha haD hscalar hpast hnearD
    ((X n).sample.region_subset_of_radius_le D.outer hinnerRadius)
    (X n).sample.region_nonempty (X n).sample.lifetime_le
    (X n).sample.cylinder (X n).sample.birth_identity
  refine ⟨⟨D.outer, D.radius_eq, D.eta_eq, D.comparison_eq,
    (min_le_min_left _ hnext).trans hcontrolD.1, ?_⟩⟩
  intro s hs y
  have hbound := hcontrolD.2 s ⟨hs.1, hs.2.trans_le (min_le_min_left _ hnext)⟩ y
  simpa only [max_eq_left hnewK] using hbound

end PoincareConjecture.M44
