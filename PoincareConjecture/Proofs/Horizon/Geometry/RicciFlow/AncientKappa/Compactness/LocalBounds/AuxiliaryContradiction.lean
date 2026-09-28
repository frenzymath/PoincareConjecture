import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.ScalarBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Nonflatness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Noncollapse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance auxiliaryCarrierConnected (C : FlowCarrier 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

theorem false_of_eventually_bounded_curvature_and_positive_volume_ratio
    (P : M23NormalizedKappaCompactnessPredecessors) {B ν : ℝ}
    (hB : 0 ≤ B) (hν : 0 < ν)
    (hbound : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ∀ t : ℝ, t ≤ 0 → ∀ x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base r,
        |((S.term k).flow.flow.connection t).curvatureTensorNorm x| ≤ B)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (ν * r ^ 3) ≤ calibratedMetricVolume ((S.term k).flow.flow.metric 0)
        (((S.term k).flow.flow.metric 0).ball (S.term k).base r)) : False := by
  have hcontrol := S.allTimeCurvatureControl_of_eventually P
    (fun r hr ↦ ⟨B, hB, hbound r hr⟩)
  obtain ⟨G, hcomplete, hnorm, hoperator, hvol⟩ :=
    S.exists_complete_bounded_positive_volume_interior_limit P hB hbound hvolume
  obtain ⟨δ, hδpos, hδone, hbuffer⟩ := S.exists_base_scalar_positive_time_buffer P hcontrol
  let s := 1 - δ
  have hspos : 0 < s := by dsimp [s]; linarith
  have hsone : s < 1 := by dsimp [s]; linarith
  have hscalar : ∀ᶠ k in atTop,
      (1 : ℝ) / 2 ≤ ((S.term k).flow.flow.connection (s - 1)).scalarCurvature (S.term k).base :=
    Eventually.of_forall fun k ↦ hbuffer k (s - 1) ⟨by dsimp [s]; linarith,
      by dsimp [s]; linarith⟩
  have hpositive := S.interiorLimit_base_curvatureTensorNorm_pos_of_scalar_buffer
    G hsone (by norm_num : (0 : ℝ) < 1 / 2) hscalar
  have hshift : (fun t : ℝ ↦ t + s) '' Iic 0 ⊆ Iio 1 := by
    rintro _ ⟨t, ht, rfl⟩
    change t + s < 1
    linarith [show t ≤ 0 from ht]
  let F : RicciFlow 3 G.limitCarrier.carrier (Iic 0) :=
    G.limitFlow.translate s hshift ordConnected_Iic
      ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  have hcompleteF : ∀ t ≤ 0, MetricComplete (F.metric t) := by
    intro t ht
    exact hcomplete (t + s) (by change t + s < 1; linarith)
  have hoperatorF : ∀ t ≤ 0, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x := by
    intro t ht x
    exact hoperator (t + s) (by change t + s < 1; linarith) x
  have hnormF : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ B := by
    intro t ht x
    exact hnorm (t + s) (by change t + s < 1; linarith) x
  have hpositiveF : ∃ p, 0 < (F.connection 0).scalarCurvature p := by
    refine ⟨G.base, ?_⟩
    have hp := hpositive.trans_le
      ((G.limitFlow.connection s).curvatureTensorNorm_le_scalarCurvature_sharp
        (P.tensor_calculus 3 G.limitCarrier.carrier (G.limitFlow.metric s)
          (G.limitFlow.connection s)) G.base (hoperator s hsone G.base))
    change 0 < (G.limitFlow.connection (0 + s)).scalarCurvature G.base
    rw [zero_add]
    exact hp
  have hnonflat := F.scalarCurvature_positive_somewhere_of_bounded_ancient_of_m23_predecessors
    P hcompleteF hoperatorF hB hnormF hpositiveF
  have hnc := S.interiorLimit_metricKappaNoncollapsed P G hcomplete
  let K : AncientKappaSolution 3 G.limitCarrier.carrier := {
    flow := F
    kappa := kappa / 27
    kappa_pos := div_pos S.kappa_pos (by norm_num)
    complete := hcompleteF
    nonnegative_curvature_operator := hoperatorF
    bounded_curvature := fun t ht ↦ ⟨B, hB, fun x ↦ by
      rw [abs_of_nonneg (show 0 ≤ (F.connection t).curvatureTensorNorm x from Real.sqrt_nonneg _)]
      exact hnormF t ht x⟩
    nonflat := fun t ht ↦ by
      obtain ⟨x, hx⟩ := hnonflat t ht
      refine ⟨x, ?_⟩
      have h := (F.connection t).scalarCurvature_le_curvatureTensorNorm_sharp x
      norm_num at h
      intro hz
      rw [hz, mul_zero] at h
      exact hx.not_ge h
    noncollapsed := by
      intro r₀ hr₀ t ht p r hr hrr₀ hcurv
      apply (hnc (t + s) (by linarith)).2 p r hr
      intro q hq
      exact hcurv t ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩ q hq
  }
  have havr : asymptoticVolumeRatio (G.limitFlow.metric 0) G.base = 0 := by
    have h := P.zero_avr G.limitCarrier.carrier K (-s) (by linarith) G.base
    change asymptoticVolumeRatio (G.limitFlow.metric (-s + s)) G.base = 0 at h
    simpa only [neg_add_cancel] using h
  have hν' : 0 < ν / Real.exp (27 * B) ^ 6 := by positivity
  have hlower : ENNReal.ofReal (ν / Real.exp (27 * B) ^ 6) ≤
      asymptoticVolumeRatio (G.limitFlow.metric 0) G.base := by
    apply le_sInf
    rintro _ ⟨r, rfl⟩
    have h := ENNReal.div_le_div_right (hvol r.1 r.2) (ENNReal.ofReal r.1 ^ 3)
    have hcancel : (ν / Real.exp (27 * B) ^ 6) * r.1 ^ 3 / r.1 ^ 3 =
        ν / Real.exp (27 * B) ^ 6 := mul_div_cancel_right₀ _ (pow_ne_zero _ r.2.ne')
    rw [← ENNReal.ofReal_pow r.2.le,
      ← ENNReal.ofReal_div_of_pos (pow_pos r.2 3), hcancel] at h
    simpa only [metricBallVolumeRatio, ENNReal.ofReal_pow r.2.le] using h
  rw [havr] at hlower
  exact (ENNReal.ofReal_pos.mpr hν').not_ge hlower

end PoincareConjecture.NormalizedKappaSolutionSequence
