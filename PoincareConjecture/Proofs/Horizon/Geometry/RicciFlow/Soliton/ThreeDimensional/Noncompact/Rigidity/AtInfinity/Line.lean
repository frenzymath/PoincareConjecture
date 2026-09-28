import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.AtInfinity.UnscaledLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.LimitNoncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SelectedComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

noncomputable section

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

private theorem line_of_escaping_static_source
    {C : FlowCarrier.{0} 3} {T : ℝ} (F : RicciFlow 3 C.carrier (Iio T)) (hT : 0 < T)
    (p : C.carrier) (q : ℕ → C.carrier)
    (hcomplete : MetricComplete (F.metric 0))
    (hsec : (F.connection 0).NonnegativeSectionalCurvature)
    (hescape : Tendsto (fun k => ((F.metric 0).edist p (q k)).toReal) atTop atTop)
    (L : AncientPointedGeometricConvergence (fun _ => C) (fun _ => F.metric) q T)
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0)) :
    letI := L.limitCarrier.metricSpaceOf (L.limitFlow.metric 0)
    ∃ γ : ℝ → L.limitCarrier.carrier, Isometry γ ∧ γ 0 = L.base := by
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let g := F.metric 0
  let d := fun i => (g.edist p (q (L.subsequence i))).toReal
  let r := fun i => Real.sqrt (d i + 1)
  have hd : Tendsto d atTop atTop := hescape.comp L.subsequence_strictMono.tendsto_atTop
  have hd0 (i : ℕ) : 0 ≤ d i := ENNReal.toReal_nonneg
  have hr (i : ℕ) : 0 < r i := Real.sqrt_pos.mpr (by linarith [hd0 i])
  have hrTop : Tendsto r atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_mono (fun i => by linarith) hd)
  have hsmall : Tendsto (fun i => r i / d i) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hrTop).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hd))
    have hh' : Tendsto (fun i => (1 / r i) * (1 + 1 / d i)) atTop (𝓝 0) := by
      simpa only [zero_mul] using hh
    apply hh'.congr'
    filter_upwards [hd.eventually_gt_atTop 0] with i hi
    have hsq : r i ^ 2 = d i + 1 := Real.sq_sqrt (by linarith [hd0 i])
    field_simp [(hr i).ne', hi.ne']
    nlinarith [hsq]
  obtain ⟨σ, hσ, s, minus, plus, hs, _, hsTop, hbase, hminus, hplus, hangle⟩ :=
    g.exists_selected_normalized_opposite_segments (F.connection 0) hcomplete hsec
      p (fun i => q (L.subsequence i)) r (fun _ => 1) hr (fun _ => zero_lt_one)
      hd (by simpa only [Real.sqrt_one, mul_one] using hd)
      (by simpa only [Real.sqrt_one, mul_one] using hrTop) hsmall (K := 0) le_rfl
  simp only [rescaledMetric_edist, Real.sqrt_one, ENNReal.ofReal_one, one_mul]
    at hminus hplus hangle
  apply L.exists_isometric_line_of_subsequence_opposite_segments
    (C := fun _ => C) (J := fun _ => Iio T) (fun _ => F) hT
    (fun a b hb => Filter.Eventually.of_forall fun _ _ ht => ht.2.trans_lt hb)
    hLcomplete σ hσ minus plus (fun i => (hbase i).1) (fun i => (hbase i).2.1)
    hsTop hsTop hminus hplus hangle
  intro i a ha b hb
  apply g.toponogov_corresponding_side_of_edist_segments (F.connection 0) hcomplete hsec
    (half_pos (hs i).1) (half_pos (hs i).1) (hbase i).1 (hbase i).2.1
  · intro a ha b hb
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top _ _), hminus i a ha b hb]
  · intro a ha b hb
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top _ _), hplus i a ha b hb]
  · exact ha
  · exact hb

namespace ShrinkingSolitonFlow

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)

theorem unscaledSourceFlow_centers_escape (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (t : ℝ) (ht : t < 1) :
    Tendsto (fun k => ((G.unscaledSourceFlow.metric t).edist p (q k)).toReal) atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  let K := {x : M | (G.unscaledSourceFlow.metric t).edist p x ≤ ENNReal.ofReal R}
  have hK : IsCompact K := (G.unscaledSourceFlow.metric t).isCompact_closedBall_of_metricComplete
    (G.unscaledSourceFlow_complete t ht) p R
  obtain ⟨B, hB⟩ := hK.bddAbove_image (S.metric.continuous_toReal_edist p).continuousOn
  filter_upwards [hescape.eventually_gt_atTop B] with k hk
  by_contra hnot
  have hdist : ((G.unscaledSourceFlow.metric t).edist p (q k)).toReal ≤ R :=
    (lt_of_not_ge hnot).le
  have hmem : q k ∈ K := by
    change (G.unscaledSourceFlow.metric t).edist p (q k) ≤ ENNReal.ofReal R
    rw [← ENNReal.ofReal_toReal ((G.unscaledSourceFlow.metric t).edist_ne_top p (q k))]
    exact ENNReal.ofReal_le_ofReal hdist
  exact (not_le.mpr hk) (hB (mem_image_of_mem _ hmem))

theorem unscaledPointedLimit_line (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (L : AncientPointedGeometricConvergence
      (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
      (fun _ => G.unscaledSourceFlow.shrink.metric)
      (fun k => equivShrink M (q k)) 1)
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0))
    (t : ℝ) (ht : t < 1) :
    letI := L.limitCarrier.metricSpaceOf (L.limitFlow.metric t)
    ∃ γ : ℝ → L.limitCarrier.carrier, Isometry γ ∧ γ 0 = L.base := by
  let C := AncientRescalingSequence.smallRescalingCarrier (n := 3) (M := M)
  let F : RicciFlow 3 C.carrier (Iio (1 - t)) :=
    G.unscaledSourceFlow.shrink.translate t
      (by
        rintro _ ⟨s, hs, rfl⟩
        change s < 1 - t at hs
        change s + t < 1
        linarith)
      ordConnected_Iio ⟨-t - 1, by change -t - 1 < 1 - t; linarith,
        -t, by change -t < 1 - t; linarith, by linarith⟩
  have hFcomplete : MetricComplete (F.metric 0) := by
    change MetricComplete (G.unscaledSourceFlow.shrink.metric (0 + t))
    rw [zero_add]
    exact (G.unscaledSourceFlow.shrink_metricComplete_iff t).mpr
      (G.unscaledSourceFlow_complete t ht)
  have hsec : (F.connection 0).NonnegativeSectionalCurvature := by
    intro x v w
    apply (F.connection 0).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
    change (G.unscaledSourceFlow.shrink.connection (0 + t)).NonnegativeCurvatureOperator x
    rw [zero_add]
    exact (G.unscaledSourceFlow.shrink_nonnegativeCurvatureOperator_iff t x).mpr
      (G.unscaledSourceFlow_nonnegativeCurvatureOperator t ht _)
  have hescapeF : Tendsto (fun k => ((F.metric 0).edist
      (equivShrink M p) (equivShrink M (q k))).toReal) atTop atTop := by
    change Tendsto (fun k => ((G.unscaledSourceFlow.shrink.metric (0 + t)).edist
      (equivShrink M p) (equivShrink M (q k))).toReal) atTop atTop
    simpa only [zero_add, G.unscaledSourceFlow.shrink_edist, Equiv.symm_apply_apply] using
      G.unscaledSourceFlow_centers_escape p q hescape t ht
  have hLcomplete : (L.shiftTime t).limitCarrier.metricComplete
      ((L.shiftTime t).limitFlow.metric 0) := by
    change L.limitCarrier.metricComplete (L.limitFlow.metric (0 + t))
    rw [zero_add]
    exact G.unscaledPointedLimit_complete L hcomplete t ht
  have hline := line_of_escaping_static_source F (sub_pos.mpr ht) (equivShrink M p)
    (fun k => equivShrink M (q k)) hFcomplete hsec hescapeF (L.shiftTime t) hLcomplete
  change (letI := L.limitCarrier.metricSpaceOf (L.limitFlow.metric (0 + t))
    ∃ γ : ℝ → L.limitCarrier.carrier, Isometry γ ∧ γ 0 = L.base) at hline
  rw [zero_add] at hline
  exact hline

end ShrinkingSolitonFlow

end PoincareConjecture
