import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Ancient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SelectedComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

set_option maxHeartbeats 1000000 in
theorem exists_isometric_line_of_open_selected_rescalings
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (F : RicciFlow (m + 1) M (Iio 0))
    (hcomplete : ∀ t < 0, MetricComplete (F.metric t))
    (hoperator : ∀ t < 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hmonotone : ∀ x, MonotoneOn (fun t => (F.connection t).scalarCurvature x) (Iio 0))
    (t₀ : ℝ) (ht₀ : t₀ < 0) (p : M) (q : ℕ → M) (r Q : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hQ : ∀ i, 0 < Q i)
    (hscalar : ∀ i, ∀ x ∈ (F.metric t₀).ball (q i) (r i),
      (F.connection t₀).scalarCurvature x ≤ 4 * Q i)
    (hdtop : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    (hDtop : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal * Real.sqrt (Q i))
      atTop atTop)
    (hLtop : Tendsto (fun i => r i * Real.sqrt (Q i)) atTop atTop)
    (hsmall : Tendsto (fun i => r i / ((F.metric t₀).edist p (q i)).toReal) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ)
    (G : AncientPointedGeometricConvergence
      (fun _ => (FlowCarrier.ofConnectedManifold (m + 1) M).shrink)
      (fun i t => (F.openAncientRescaleAt (Q i) (hQ i) t₀).shrink.metric (t - δ))
      (fun i => equivShrink M (q i)) δ)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base := by
  let H := fun i => F.openAncientRescaleAt (Q i) (hQ i) t₀
  let L := fun i => r i * Real.sqrt (Q i)
  have htime (i : ℕ) (s : ℝ) (hs : s ≤ 0) : t₀ + s / Q i < 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)).trans_lt ht₀
  have hwindow (i : ℕ) (a : ℝ) : Icc a 0 ⊆ interior (Iio (-t₀ * Q i)) := by
    rw [isOpen_Iio.interior_eq]
    intro s hs
    exact hs.2.trans_lt (mul_pos (neg_pos.mpr ht₀) (hQ i))
  have hcH (i : ℕ) (s : ℝ) (hs : s ≤ 0) : MetricComplete ((H i).metric s) := by
    exact F.parabolicRescale_metricComplete _ _ _ _ _ _ _ (hcomplete _ (htime i s hs))
  have hoH (i : ℕ) (s : ℝ) (hs : s ≤ 0) (x : M) :
      ((H i).connection s).NonnegativeCurvatureOperator x := by
    exact F.parabolicRescale_nonnegativeCurvatureOperator _ _ _ _ _ _ _ _
      (hoperator _ (htime i s hs) x)
  have hmetric0 (i : ℕ) : (H i).metric 0 = rescaledMetric (F.metric t₀) (Q i) (hQ i) := by
    change rescaledMetric (F.metric (t₀ + 0 / Q i)) (Q i) (hQ i) = _
    rw [zero_div, add_zero]
  have hball (i : ℕ) : ((H i).metric 0).ball (q i) (L i) =
      (F.metric t₀).ball (q i) (r i) := by
    rw [hmetric0, rescaledMetric_ball_allDimensions]
    dsimp only [L]
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (hQ i)).ne']
  have hscalarH (i : ℕ) (s : ℝ) (hs : s ≤ 0) (x : M)
      (hx : x ∈ ((H i).metric 0).ball (q i) (L i)) :
      ((H i).connection s).scalarCurvature x ≤ 4 := by
    have hst : t₀ + s / Q i ≤ t₀ :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)
    have h := ((hmonotone x) (hst.trans_lt ht₀) ht₀ hst).trans
        (hscalar i x ((hball i) ▸ hx))
    dsimp only [H, openAncientRescaleAt]
    rw [parabolicRescale_scalarCurvature]
    calc
      _ ≤ (Q i)⁻¹ * (4 * Q i) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (hQ i).le)
      _ = 4 := by field_simp [(hQ i).ne']
  have hRic (i : ℕ) (s : ℝ) (hs : s ≤ 0) (x : M)
      (v : TangentSpace (𝓡 (m + 1)) x) : 0 ≤ ((H i).connection s).ricci x v v :=
    (((H i).connection s).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M ((H i).metric s) ((H i).connection s))
      x (hoH i s hs x) v).1
  have hupper (i : ℕ) (s : ℝ) (hs : s ∈ Icc (-δ) 0) (x : M)
      (hx : x ∈ ((H i).metric 0).ball (q i) (L i)) (v : TangentSpace (𝓡 (m + 1)) x) :
      ((H i).connection s).ricci x v v ≤ 4 * ((H i).metric s).inner x v v := by
    have hn : 0 ≤ ((H i).metric s).inner x v v := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
        ⟨((H i).metric s).toRiemannianMetric⟩
      exact @real_inner_self_nonneg (TangentSpace (𝓡 (m + 1)) x) _ _ v
    exact ((((H i).connection s).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M ((H i).metric s) ((H i).connection s))
      x (hoH i s hs.2 x) v).2).trans
        (mul_le_mul_of_nonneg_right (hscalarH i s hs.2 x hx) hn)
  have hsec : (F.connection t₀).NonnegativeSectionalCurvature := by
    intro x v w
    exact (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀ x) v w
  obtain ⟨σ, hσ, s, minus, plus, hs, _, hstop, hbase, hminus, hplus, hangle⟩ :=
    (F.metric t₀).exists_selected_normalized_opposite_segments (F.connection t₀)
      (hcomplete t₀ ht₀) hsec p (fun i => q (G.subsequence i))
      (fun i => r (G.subsequence i)) (fun i => Q (G.subsequence i))
      (fun i => hr (G.subsequence i)) (fun i => hQ (G.subsequence i))
      (hdtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hDtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hLtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hsmall.comp G.subsequence_strictMono.tendsto_atTop)
      (K := 4 * Real.exp (4 * δ)) (by positivity)
  apply exists_isometric_line_of_small_selected_terminal_segments hC hm
    (fun i => Iio (-t₀ * Q i)) H hδ (Λ := 4) (by norm_num) (scale := 1) (by norm_num)
    (fun i a => (hwindow i a).trans interior_subset) (fun i => hwindow i (-δ))
    (fun i t ht => hcH i t ht.2) (fun i t ht => hRic i t ht.2) q L hupper G hGcomplete
    σ hσ s (fun i => (hs i).1) (fun i => (hs i).2) minus plus
    (fun i => s i / 2) (fun i => s i / 2)
    (fun i => half_pos (hs i).1) (fun i => half_pos (hs i).1)
    (fun i => (hbase i).1) (fun i => (hbase i).2.1)
  · intro i a ha b hb
    rw [hmetric0]
    exact hminus i a ha b hb
  · intro i a ha b hb
    rw [hmetric0]
    exact hplus i a ha b hb
  · intro i
    rw [hmetric0]
    exact (hbase i).2.2.1
  · intro i
    rw [hmetric0]
    exact (hbase i).2.2.2
  · exact hstop
  · exact hstop
  · simpa only [hmetric0] using hangle
  · intro i α β A B hA hB hα0 hβ0 hα hβ
    let j := G.subsequence (σ i)
    have hsecH : ((H j).connection (-δ)).NonnegativeSectionalCurvature := by
      intro x v w
      exact ((H j).connection (-δ)).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoH j (-δ) (by linarith) x) v w
    apply ((H j).metric (-δ)).toponogov_corresponding_side_of_edist_segments
      ((H j).connection (-δ)) (hcH j (-δ) (by linarith)) hsecH hA hB hα0 hβ0
    · intro a ha b hb
      rw [← ENNReal.ofReal_toReal (((H j).metric (-δ)).edist_ne_top _ _), hα a ha b hb]
    · intro a ha b hb
      rw [← ENNReal.ofReal_toReal (((H j).metric (-δ)).edist_ne_top _ _), hβ a ha b hb]

end PoincareConjecture.RicciFlow
