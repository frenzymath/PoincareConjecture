import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_StageFamilyComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_MaximalAlternative
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_ObservationModels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

theorem prepared_counterexamples_contradiction
    (P : M44CapPersistencePredecessors.{u})
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    {start rNext A eta theta Rinner : ℝ}
    (hA : 0 < A) (hetaTarget : 0 < eta) (htheta : 0 < theta) (htheta1 : theta < 1)
    {cutoffs : ℕ → ℝ}
    (X : ∀ n, PreparedCapCounterexample.{u}
      setup start rNext A eta theta (cutoffs n) Rinner)
    (hcutoffs : Tendsto cutoffs atTop (𝓝 0))
    (heta : Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0))
    {c R0 T K : ℝ} (hc : 0 ≤ c) (hctheta : c ≤ theta)
    (hlim : Tendsto (fun n => (X n).sample.lifetime) atTop (𝓝 c))
    (hinnerR0 : Rinner < R0) (hT : 0 < T) (hcT : c < T) (hK : 0 < K)
    (hstage : CapSequenceStage X R0 T K) : False := by
  obtain ⟨Ralt, accuracy, compact, hARalt, haccuracy, hcompact, hinside, halt⟩ :=
    exists_maximal_cap_alternative_cutoff P standard (eta := eta)
      hA htheta.le htheta1 hK
  let R := max R0 Ralt
  have hR0 : R0 ≤ R := le_max_left _ _
  have hRalt : Ralt ≤ R := le_max_right _ _
  obtain ⟨eta0, delta0, heta0, hdelta0, halternative⟩ := halt R hRalt
  let closedBall := {x : StandardCapSpace |
    setup.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal A}
  have hclosed : IsCompact closedBall :=
    M36.standard_closed_ball_compact setup.standard_initial hA.le
  have herrorPos : 0 < eta ^ 2 := sq_pos_of_pos hetaTarget
  have hsphere := eventually_stage_twoJet_comparison P standard unique hstage heta hlim
    hT hK htheta htheta1 hc hctheta hcompact haccuracy
  have hjets := eventually_stage_metricJetError_le P standard unique hstage heta hlim
    hT hK htheta htheta1 hc hctheta ⌊eta⁻¹⌋₊ hclosed herrorPos
  have hfalse : ∀ᶠ _n in (atTop : Filter ℕ), False := by
    filter_upwards [hstage R hR0, hcutoffs.eventually (gt_mem_nhds hdelta0),
      heta.eventually (gt_mem_nhds heta0), hlim.eventually (gt_mem_nhds hcT),
      hsphere, hjets] with n hn hdeltaN hetaN hlifeN hsphereN hjetsN
    obtain ⟨D⟩ := hn
    have hinnerRadius : (X n).sample.radius ≤ D.outer.radius := by
      rw [(X n).radius_eq, D.radius_eq]
      exact hinnerR0.le.trans hR0
    have hlife : D.outer.lifetime = (X n).sample.lifetime :=
      le_antisymm ((X n).sample.lifetime_antitone D.outer hinnerRadius)
        (by simpa only [min_eq_left hlifeN.le] using D.survival)
    have htime {s : ℝ} (hs : s ∈ Ico (0 : ℝ) D.outer.lifetime) :
        s ∈ Ico (0 : ℝ) (min (X n).sample.lifetime T) := by
      rw [min_eq_left hlifeN.le, ← hlife]
      exact hs
    have hcurv : ∀ s ∈ Ico (0 : ℝ) D.outer.lifetime, ∀ y,
        (D.outer.ordinary.flow.connection s).curvatureTensorNorm y ≤ K :=
      fun s hs y => D.curvature s (htime hs) y
    have hsource {x : StandardCapSpace}
        (hx : x ∈ setup.standard_initial.metric.ball 0 R) : x ∈ D.outer.chart.source := by
      rwa [D.outer.toCylinderCompactnessSample.source_eq, D.radius_eq]
    have hsphereD := fun s (hs : s ∈ Ico (0 : ℝ) D.outer.lifetime)
        x (hx : x ∈ compact) =>
      hsphereN D.outer.toCylinderCompactnessSample D.comparison_eq s (htime hs) hs.2 x hx
        (hsource ((hinside hx).trans_le (ENNReal.ofReal_le_ofReal hRalt)))
    have hfamily : ∃ bound : ℝ, bound < eta ^ 2 ∧
        ∀ s (hs : s ∈ Ico (0 : ℝ) D.outer.lifetime),
        ∀ x ∈ (X n).data.flow.standard_initial.metric.ball 0 A,
          singularMetricJetErrorSquared ((X n).data.observation.standard_flow.metric s)
            ((X n).data.observation.standard_flow.connection s)
            (fun y v => D.outer.cylinder.pullbackInner s hs (D.outer.chart y)
              (mfderiv (𝓡 3) (𝓡 3) D.outer.chart y (v 0))
              (mfderiv (𝓡 3) (𝓡 3) D.outer.chart y (v 1))) ⌊eta⁻¹⌋₊ x ≤ bound := by
      refine ⟨eta ^ 2 / 2, half_lt_self herrorPos, ?_⟩
      intro s hs x hx
      have hxA : x ∈ setup.standard_initial.metric.ball 0 A := by
        simpa only [(X n).data.fixed_scales.standard_initial_eq] using hx
      have hxClosed : x ∈ closedBall := by
        have hxStrict : setup.standard_initial.metric.edist 0 x < ENNReal.ofReal A := hxA
        change setup.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal A
        exact hxStrict.le
      have hxSource : x ∈ D.outer.chart.source :=
        hsource (hxA.trans_le (ENNReal.ofReal_le_ofReal (hARalt.le.trans hRalt)))
      have hsOne : s ∈ Ico (0 : ℝ) 1 :=
        ⟨hs.1, (hs.2.trans_le
          (D.outer.lifetime_le.trans (X n).data.assignedDuration_le)).trans htheta1⟩
      exact hjetsN D.outer.toCylinderCompactnessSample D.comparison_eq s (htime hs) hs.2
        x hxClosed hxSource ((X n).data.observation.standard_flow.metric s)
        ((X n).data.observation_metric_eq standard unique hsOne)
        ((X n).data.observation.standard_flow.connection s)
    have hlink : (((X n).data.flow.event (X n).data.time (X n).data.is_surgery).necks
        (X n).data.cap).neck.epsilon ≤
          (X n).data.flow.local_constants.comparison_delta D.outer.eta := by
      simpa only [D.eta_eq] using (X n).comparison_neck
    exact (X n).data.failure (halternative (X n).data.flow (X n).data.observation setup
      (X n).data.fixed_scales hdeltaN.le (X n).data.time (X n).data.is_surgery
      (X n).data.cap (fun _ hs => (X n).data.assigned_time_mem hs) (X n).data.pinched
      D.outer D.radius_eq (by simpa only [D.eta_eq] using hetaN.le) hlink
      (X n).data.observation_lifetime_one hcurv hsphereD hfamily)
  exact hfalse.exists.choose_spec

end PoincareConjecture.M44
