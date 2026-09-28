import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Sequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.BackwardVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Interior
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Inheritance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Preservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.VolumeBounds












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance localBoundsLimitCarrierConnected (C : FlowCarrier 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)



theorem interiorLimit_base_curvatureTensorNorm_pos_of_scalar_buffer
    (G : AncientPointedGeometricConvergence (fun k ↦ (S.term k).carrier)
      (fun k t ↦ (S.term k).flow.flow.metric (t - 1)) (fun k ↦ (S.term k).base) 1)
    {s c : ℝ} (hs : s < 1) (hc : 0 < c)
    (hscalar : ∀ᶠ k in atTop,
      c ≤ ((S.term k).flow.flow.connection (s - 1)).scalarCurvature (S.term k).base) :
    0 < (G.limitFlow.connection s).curvatureTensorNorm G.base := by
  obtain ⟨a, b, ha, hb, hb1, hsw⟩ := exists_ancient_window_of_isCompact
    (by norm_num : (0 : ℝ) < 1) isCompact_singleton (singleton_subset_iff.mpr hs)
  let Fseq (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ ↦ t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  have hsub (k : ℕ) : Ioo a b ⊆ (fun t : ℝ ↦ t - 1) ⁻¹' Iic 0 := by
    intro t ht
    change t - 1 ≤ 0
    linarith [ht.2]
  let W := G.window Fseq (ha.trans hb) hb1.le 0 (fun k ↦ hsub (G.subsequence (k + 0)))
  have hconv := W.tendsto_curvatureTensorNorm s (hsw (mem_singleton s)) G.base
  change Tendsto (fun k ↦ ((S.term (G.subsequence (k + 0))).flow.flow.connection (s - 1)).curvatureTensorNorm
      (G.embedding (k + 0) G.base)) atTop
    (𝓝 ((G.limitFlow.connection s).curvatureTensorNorm G.base)) at hconv
  simp only [Nat.add_zero, G.base_preserving] at hconv
  have htrace : c ≤ 9 * (G.limitFlow.connection s).curvatureTensorNorm G.base := by
    apply ge_of_tendsto (tendsto_const_nhds.mul hconv (a := (9 : ℝ)))
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hscalar] with k hk
    exact hk.trans ((le_abs_self _).trans (by
      simpa only [Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using ((S.term (G.subsequence k)).flow.flow.connection (s - 1)).abs_scalarCurvature_le_curvatureTensorNorm
        (S.term (G.subsequence k)).base))
  linarith



theorem exists_complete_bounded_interior_geometric_limit
    (P : M23NormalizedKappaCompactnessPredecessors) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ∀ t : ℝ, t ≤ 0 → ∀ x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base r,
        |((S.term k).flow.flow.connection t).curvatureTensorNorm x| ≤ B) :
    ∃ G : AncientPointedGeometricConvergence (fun k ↦ (S.term k).carrier)
        (fun k t ↦ (S.term k).flow.flow.metric (t - 1)) (fun k ↦ (S.term k).base) 1,
      (∀ t ∈ Iio 1, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
      (∀ t ∈ Iio 1, ∀ x : G.limitCarrier.carrier,
        (G.limitFlow.connection t).curvatureTensorNorm x ≤ B) ∧
      ∀ t ∈ Iio 1, ∀ x : G.limitCarrier.carrier,
        (G.limitFlow.connection t).NonnegativeCurvatureOperator x := by
  have hcontrol := S.allTimeCurvatureControl_of_eventually P (fun r hr ↦ ⟨B, hB, hbound r hr⟩)
  obtain ⟨G, hcomplete⟩ := S.exists_complete_interior_geometric_limit P hcontrol
  let Fseq (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ ↦ t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  have htime : ∀ a b : ℝ, b < 1 → ∀ᶠ k : ℕ in atTop,
      Icc a b ⊆ (fun t : ℝ ↦ t - 1) ⁻¹' Iic 0 := by
    intro a b hb
    exact Eventually.of_forall fun k t ht ↦ by
      change t - 1 ≤ 0
      linarith [ht.2]
  have hnorm : ∀ t ∈ Iio 1, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).curvatureTensorNorm x ≤ B := by
    apply G.curvatureTensorNorm_le_of_uniform_ball_bound Fseq (by norm_num) htime
    intro a b hb r hr
    filter_upwards [hbound r hr] with k hk t ht x hx
    have ht0 : t - 1 ≤ 0 := by linarith [ht.2]
    have hx0 := P.ball_monotone (S.term k).carrier.carrier (S.term k).flow
      (t - 1) 0 ht0 le_rfl (S.term k).base r hx
    exact (le_abs_self _).trans (hk (t - 1) ht0 x hx0)
  refine ⟨G, ?_, hnorm, ?_⟩
  · exact S.interiorLimit_complete G P hcontrol hcomplete
  · exact S.interiorLimit_nonnegativeCurvatureOperator G




theorem exists_complete_bounded_positive_volume_interior_limit
    (P : M23NormalizedKappaCompactnessPredecessors) {B ν : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ∀ t : ℝ, t ≤ 0 → ∀ x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base r,
        |((S.term k).flow.flow.connection t).curvatureTensorNorm x| ≤ B)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (ν * r ^ 3) ≤ calibratedMetricVolume ((S.term k).flow.flow.metric 0)
        (((S.term k).flow.flow.metric 0).ball (S.term k).base r)) :
    ∃ G : AncientPointedGeometricConvergence (fun k ↦ (S.term k).carrier)
        (fun k t ↦ (S.term k).flow.flow.metric (t - 1)) (fun k ↦ (S.term k).base) 1,
      (∀ t ∈ Iio 1, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
      (∀ t ∈ Iio 1, ∀ x : G.limitCarrier.carrier,
        (G.limitFlow.connection t).curvatureTensorNorm x ≤ B) ∧
      (∀ t ∈ Iio 1, ∀ x : G.limitCarrier.carrier,
        (G.limitFlow.connection t).NonnegativeCurvatureOperator x) ∧
      ∀ r : ℝ, 0 < r → ENNReal.ofReal ((ν / Real.exp (27 * B) ^ 6) * r ^ 3) ≤
        calibratedMetricVolume (G.limitFlow.metric 0) ((G.limitFlow.metric 0).ball G.base r) := by
  obtain ⟨G, hcomplete, hnorm, hoperator⟩ :=
    S.exists_complete_bounded_interior_geometric_limit P hB hbound
  refine ⟨G, hcomplete, hnorm, hoperator, ?_⟩
  let Fseq (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ ↦ t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  have htime : ∀ a b : ℝ, b < 1 → ∀ᶠ k : ℕ in atTop,
      Icc a b ⊆ (fun t : ℝ ↦ t - 1) ⁻¹' Iic 0 := by
    intro a b hb
    exact Eventually.of_forall fun k t ht ↦ by
      change t - 1 ≤ 0
      linarith [ht.2]
  have hvol := G.ball_volume_lower_bound_of_metricComplete_zero Fseq (by norm_num)
    htime (hcomplete 0 (by norm_num)) (ν / Real.exp (27 * B) ^ 6) (by
      intro r hr
      have hv := S.eventually_earlier_ball_volume_lower_bound
        (by norm_num : (0 : ℝ) ≤ 1) hbound hvolume r hr
      filter_upwards [hv] with k hk
      simpa only [Fseq, RicciFlow.bufferedExpandingFlow_metric, zero_sub, mul_one,
        calibratedMetricVolume_eq_volumeMeasure] using hk)
  intro r hr
  rw [calibratedMetricVolume_eq_volumeMeasure]
  exact hvol r hr

end PoincareConjecture.NormalizedKappaSolutionSequence
