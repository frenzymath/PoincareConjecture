import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.Monotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem tendsto_ball_volume_div_pow_at_zero
    (g : RiemannianMetric n M) (p : M) :
    Tendsto (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n)
      (𝓝[>] 0) (𝓝 (euclideanUnitBallVolume n)) := by
  have h := (ENNReal.continuousAt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).tendsto.comp
    (g.tendsto_volumeMeasure_ball_div_euclidean p)
  have h' := h.mul_const (euclideanUnitBallVolume n)
  simp only [ENNReal.toReal_one, one_mul] at h'
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  dsimp only [Function.comp_apply]
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal
    (mul_nonneg (euclideanUnitBallVolume_nonneg n) (pow_nonneg (le_of_lt hr) n))]
  have hω := (euclideanUnitBallVolume_pos n).ne'
  have hr0 : r ≠ 0 := ne_of_gt hr
  field_simp

private theorem tendsto_ball_radius_shift {f : ℝ → ℝ} {V C : ℝ}
    (h : Tendsto (fun r => f r / r ^ n) atTop (𝓝 V)) :
    Tendsto (fun r => f (r + C) / r ^ n) atTop (𝓝 V) := by
  have hshift : Tendsto (fun r => f (r + C) / (r + C) ^ n) atTop (𝓝 V) :=
    h.comp (tendsto_atTop_add_const_right atTop C tendsto_id)
  have hfactor : Tendsto (fun r : ℝ => ((r + C) / r) ^ n) atTop (𝓝 1) := by
    have hz : Tendsto (fun r : ℝ => C / r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have haux : Tendsto (fun r : ℝ => (1 + C / r) ^ n) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hz).pow n
    apply haux.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [add_div, div_self hr.ne']
  have hprod : Tendsto
      (fun r => (f (r + C) / (r + C) ^ n) * ((r + C) / r) ^ n)
      atTop (𝓝 V) := by simpa only [mul_one] using hshift.mul hfactor
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-C))] with r hr
  have hr0 : 0 < r := (le_max_left _ _).trans_lt hr
  have hsum : 0 < r + C := by
    have := (le_max_right 0 (-C)).trans_lt hr
    linarith
  rw [div_pow]
  field_simp

variable [SecondCountableTopology M]

theorem asymptoticVolumeRatio_eq_of_preconnected
    [PreconnectedSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p q : M) : g.asymptoticVolumeRatio p = g.asymptoticVolumeRatio q := by
  have hle (x y : M) : g.asymptoticVolumeRatio x ≤ g.asymptoticVolumeRatio y := by
    apply le_of_tendsto_of_tendsto
      (g.tendsto_asymptoticVolumeRatio D hn hc hRic x)
      (tendsto_ball_radius_shift (C := (g.edist y x).toReal)
        (g.tendsto_asymptoticVolumeRatio D hn hc hRic y))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    apply div_le_div_of_nonneg_right _ (pow_nonneg hr.le n)
    apply ENNReal.toReal_mono (g.ball_volume_ne_top_of_metricComplete hc y _)
    apply measure_mono
    intro z hz
    change g.edist y z < ENNReal.ofReal (r + (g.edist y x).toReal)
    apply (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top y z)).mpr
    have hz' : (g.edist x z).toReal < r :=
      (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top x z)).mp hz
    have := g.toReal_edist_triangle y x z
    linarith
  exact le_antisymm (hle p q) (hle q p)

theorem ball_volume_div_pow_le_euclideanUnitBallVolume
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M) {r : ℝ} (hr : 0 < r) :
    (g.volumeMeasure (g.ball p r)).toReal / r ^ n ≤ euclideanUnitBallVolume n := by
  apply ge_of_tendsto (g.tendsto_ball_volume_div_pow_at_zero p)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with s hs hsr
  exact g.antitoneOn_ball_volume_div_pow D hn hc hRic p hs hr hsr.le

theorem volumeMeasure_ball_eq_euclidean_of_maximal_asymptotic_volume
    [PreconnectedSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M)
    (hmax : Tendsto
      (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n)
      atTop (𝓝 (euclideanUnitBallVolume n)))
    (q : M) {r : ℝ} (hr : 0 < r) :
    g.volumeMeasure (g.ball q r) = ENNReal.ofReal (euclideanUnitBallVolume n * r ^ n) := by
  have hp : g.asymptoticVolumeRatio p = euclideanUnitBallVolume n :=
    tendsto_nhds_unique (g.tendsto_asymptoticVolumeRatio D hn hc hRic p) hmax
  have hq : Tendsto
      (fun s : ℝ => (g.volumeMeasure (g.ball q s)).toReal / s ^ n)
      atTop (𝓝 (euclideanUnitBallVolume n)) := by
    rw [← hp, g.asymptoticVolumeRatio_eq_of_preconnected D hn hc hRic p q]
    exact g.tendsto_asymptoticVolumeRatio D hn hc hRic q
  have hlower : euclideanUnitBallVolume n ≤
      (g.volumeMeasure (g.ball q r)).toReal / r ^ n := by
    apply le_of_tendsto hq
    filter_upwards [eventually_ge_atTop r] with s hs
    exact g.antitoneOn_ball_volume_div_pow D hn hc hRic q hr (hr.trans_le hs) hs
  have heq := le_antisymm
    (g.ball_volume_div_pow_le_euclideanUnitBallVolume D hn hc hRic q hr) hlower
  have hreal := (div_eq_iff (pow_ne_zero n hr.ne')).mp heq
  rw [← ENNReal.ofReal_toReal (g.ball_volume_ne_top_of_metricComplete hc q r), hreal]

end PoincareConjecture.RiemannianMetric
