import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.SublevelVolume.Taylor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.SublevelVolume.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] [CompactSpace M] in

theorem exists_sublevel_chart_bounds (g : RiemannianMetric 2 M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (he0 : 0 ∈ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {f : M → ℝ} (hf : ContDiffAt ℝ ∞ (f ∘ e) 0)
    (hdf : fderiv ℝ (f ∘ e) 0 = 0) {a : ℝ} (ha : 0 < a)
    (hhess : ∀ v, fderiv ℝ (fderiv ℝ (f ∘ e)) 0 v v = a * ‖v‖ ^ 2)
    (hρ : g.pullbackVolumeDensity e 0 = 1) {K : ℝ≥0} (hK : 1 < K) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball 0 r ⊆ e.source ∧
      ∀ v ∈ Metric.ball 0 r,
        a / (2 * K) * ‖v‖ ^ 2 ≤ f (e v) - f (e 0) ∧
        f (e v) - f (e 0) ≤ (a * K / 2) * ‖v‖ ^ 2 ∧
        (K : ℝ)⁻¹ ≤ g.pullbackVolumeDensity e v ∧ g.pullbackVolumeDensity e v ≤ K := by
  have hK0 : 0 < (K : ℝ) := zero_lt_one.trans hK
  let ε : ℝ := a * (1 - (K : ℝ)⁻¹)
  have hε : 0 < ε := mul_pos ha (sub_pos.mpr ((inv_lt_one₀ hK0).mpr hK))
  have hlow : a - ε = a / K := by dsimp [ε]; ring
  have hupp : a + ε ≤ a * K := by
    have h := sq_nonneg ((K : ℝ) - 1)
    have hi := mul_inv_cancel₀ hK0.ne'
    dsimp [ε]
    nlinarith [mul_nonneg ha.le h]
  have hdiff : e.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρc := (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds he0)) (hdiff.mfderiv_injective he0)).1.continuousAt
  have hdensity : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin 2)),
      (K : ℝ)⁻¹ ≤ g.pullbackVolumeDensity e v ∧ g.pullbackVolumeDensity e v ≤ K := by
    have hl : (K : ℝ)⁻¹ < g.pullbackVolumeDensity e 0 := by
      rw [hρ]; exact (inv_lt_one₀ hK0).mpr hK
    have hu : g.pullbackVolumeDensity e 0 < K := by rwa [hρ]
    filter_upwards [hρc.eventually (lt_mem_nhds hl), hρc.eventually (gt_mem_nhds hu)] with v hv hv'
    exact ⟨hv.le, hv'.le⟩
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (e.open_source.mem_nhds he0)
      ((Poincare.Analysis.eventually_quadratic_bounds_of_fderiv2 hf hdf hhess hε).and hdensity))
  refine ⟨r, hr, fun v hv => (hb hv).1, fun v hv => ?_⟩
  obtain ⟨_, ⟨hl, hu⟩, hρl, hρu⟩ := hb hv
  refine ⟨?_, ?_, hρl, hρu⟩
  · simpa only [hlow, Function.comp_apply, div_mul_eq_mul_div,
      div_div, mul_comm (K : ℝ) 2] using hl
  · have h := mul_le_mul_of_nonneg_right hupp (sq_nonneg ‖v‖)
    dsimp only [Function.comp_apply] at hu
    nlinarith

omit [CompactSpace M] in

theorem volumeMeasure_image_ball_bounds (g : RiemannianMetric 2 M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {r s : ℝ} (hball : Metric.ball 0 r ⊆ e.source) (hs : s ≤ r)
    {K : ℝ≥0} (hK : 0 < K) (hρ : ∀ v ∈ Metric.ball 0 r,
      (K : ℝ)⁻¹ ≤ g.pullbackVolumeDensity e v ∧ g.pullbackVolumeDensity e v ≤ K) :
    (K : ℝ≥0∞)⁻¹ * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) s) ≤
        g.volumeMeasure (e '' Metric.ball 0 s) ∧
      g.volumeMeasure (e '' Metric.ball 0 s) ≤
        (K : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) s) := by
  rw [g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei measurableSet_ball
    ((ball_subset_ball hs).trans hball)]
  have hl := setLIntegral_mono' (μ := volume) measurableSet_ball
    (fun v hv => ENNReal.ofReal_le_ofReal (hρ v (ball_subset_ball hs hv)).1)
  have hu := setLIntegral_mono' (μ := volume) measurableSet_ball
    (fun v hv => ENNReal.ofReal_le_ofReal (hρ v (ball_subset_ball hs hv)).2)
  constructor
  · simpa only [lintegral_const, Measure.restrict_apply_univ,
      ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < K from hK), ENNReal.ofReal_coe_nnreal] using hl
  · simpa only [lintegral_const, Measure.restrict_apply_univ,
      ENNReal.ofReal_coe_nnreal] using hu

theorem volumeMeasure_image_ball_toReal_bounds (g : RiemannianMetric 2 M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {r s : ℝ} (hball : Metric.ball 0 r ⊆ e.source) (hs : s ≤ r) (hs0 : 0 ≤ s)
    {K : ℝ≥0} (hK : 0 < K) (hρ : ∀ v ∈ Metric.ball 0 r,
      (K : ℝ)⁻¹ ≤ g.pullbackVolumeDensity e v ∧ g.pullbackVolumeDensity e v ≤ K) :
    (K : ℝ)⁻¹ * (s ^ 2 * Real.pi) ≤ (g.volumeMeasure (e '' Metric.ball 0 s)).toReal ∧
      (g.volumeMeasure (e '' Metric.ball 0 s)).toReal ≤ (K : ℝ) * (s ^ 2 * Real.pi) := by
  obtain ⟨hl, hu⟩ := g.volumeMeasure_image_ball_bounds e he hei hball hs hK hρ
  have hm : g.volumeMeasure (e '' Metric.ball 0 s) ≠ ⊤ := measure_ne_top _ _
  have hupper : (K : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) s) ≠ ⊤ := by
    finiteness
  have hl' := ENNReal.toReal_mono hm hl
  have hu' := ENNReal.toReal_mono hupper hu
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal,
    EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs0,
    ENNReal.toReal_ofReal Real.pi_pos.le] at hl' hu'
  exact ⟨hl', hu'⟩

theorem eventually_sublevel_volume_ratio_bounds (g : RiemannianMetric 2 M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (he0 : 0 ∈ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {f : M → ℝ} (hfc : Continuous f) (hf : ContDiffAt ℝ ∞ (f ∘ e) 0)
    (hdf : fderiv ℝ (f ∘ e) 0 = 0) {a : ℝ} (ha : 0 < a)
    (hhess : ∀ v, fderiv ℝ (fderiv ℝ (f ∘ e)) 0 v v = a * ‖v‖ ^ 2)
    (hρ : g.pullbackVolumeDensity e 0 = 1)
    (hmin : ∀ x, f (e 0) ≤ f x) (huniq : ∀ x, f x = f (e 0) → x = e 0)
    {K : ℝ≥0} (hK : 1 < K) :
    ∀ᶠ t in 𝓝[>] f (e 0),
      (2 * Real.pi / a) / (K : ℝ) ^ 2 ≤
          (g.volumeMeasure {x | f x < t}).toReal / (t - f (e 0)) ∧
        (g.volumeMeasure {x | f x < t}).toReal / (t - f (e 0)) ≤
          (K : ℝ) ^ 2 * (2 * Real.pi / a) := by
  have hK0 : 0 < (K : ℝ) := zero_lt_one.trans hK
  obtain ⟨r, hr, hball, hb⟩ := g.exists_sublevel_chart_bounds e he0 he hei hf hdf ha hhess hρ hK
  have hU : e '' Metric.ball 0 r ∈ 𝓝 (e 0) :=
    e.image_mem_nhds he0 (Metric.ball_mem_nhds _ hr)
  have hloc := Poincare.Topology.eventually_sublevel_subset_of_unique_min hfc hmin huniq hU
  have hsqrt : ContinuousAt (fun t : ℝ => Real.sqrt (2 * K * (t - f (e 0)) / a)) (f (e 0)) := by
    fun_prop
  have hsmall : ∀ᶠ t in 𝓝[>] f (e 0), Real.sqrt (2 * K * (t - f (e 0)) / a) < r :=
    (hsqrt.eventually (gt_mem_nhds (by simpa using hr))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hloc, hsmall, self_mem_nhdsWithin] with t htloc htsmall ht
  have hd : 0 < t - f (e 0) := sub_pos.mpr ht
  let u := Real.sqrt (2 * K * (t - f (e 0)) / a)
  let l := Real.sqrt (2 * (t - f (e 0)) / (a * K))
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 * K * (t - f (e 0)) / a := Real.sq_sqrt (by positivity)
  have hl2 : l ^ 2 = 2 * (t - f (e 0)) / (a * K) := Real.sq_sqrt (by positivity)
  have hlu : l ≤ u := by
    apply Real.sqrt_le_sqrt
    apply (div_le_div_iff₀ (mul_pos ha hK0) ha).mpr
    have hK1 : 1 ≤ (K : ℝ) ^ 2 := by have hk : (1 : ℝ) < K := hK; nlinarith
    nlinarith [mul_nonneg (mul_nonneg ha.le hd.le) (sub_nonneg.mpr hK1)]
  have hlr : l ≤ r := hlu.trans htsmall.le
  have hul : (a / (2 * K)) * u ^ 2 = t - f (e 0) := by
    rw [hu2]; field_simp
  have hll : (a * K / 2) * l ^ 2 = t - f (e 0) := by
    rw [hl2]; field_simp
  have hinner : e '' Metric.ball 0 l ⊆ {x | f x < t} := by
    rintro _ ⟨v, hv, rfl⟩
    have hvn : ‖v‖ < l := by simpa only [Metric.mem_ball, dist_zero_right] using hv
    have hvsq : ‖v‖ ^ 2 < l ^ 2 := (sq_lt_sq₀ (norm_nonneg _) hl0).mpr hvn
    have h := (hb v (Metric.ball_subset_ball hlr hv)).2.1
    have hstrict := mul_lt_mul_of_pos_left hvsq (show 0 < a * K / 2 by positivity)
    rw [hll] at hstrict
    have hlt := h.trans_lt hstrict
    exact (sub_lt_sub_iff_right _).mp hlt
  have houter : {x | f x < t} ⊆ e '' Metric.ball 0 u := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := htloc hx
    refine ⟨v, ?_, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    apply (sq_lt_sq₀ (norm_nonneg _) hu0).mp
    have h := (hb v hv).1
    have hlt : (a / (2 * K)) * ‖v‖ ^ 2 < (a / (2 * K)) * u ^ 2 := by
      rw [hul]; exact lt_of_le_of_lt h (by exact sub_lt_sub_right hx _)
    exact (mul_lt_mul_iff_right₀ (show 0 < a / (2 * K) by positivity)).mp hlt
  have hlvol := (g.volumeMeasure_image_ball_toReal_bounds e he hei hball hlr hl0
    hK0 (fun v hv => (hb v hv).2.2)).1
  have huvol := (g.volumeMeasure_image_ball_toReal_bounds e he hei hball htsmall.le hu0
    hK0 (fun v hv => (hb v hv).2.2)).2
  have hlmono := ENNReal.toReal_mono (measure_ne_top g.volumeMeasure _) (measure_mono hinner)
  have humono := ENNReal.toReal_mono (measure_ne_top g.volumeMeasure _) (measure_mono houter)
  constructor
  · apply (le_div_iff₀ hd).mpr
    have heq : (2 * Real.pi / a) / (K : ℝ) ^ 2 * (t - f (e 0)) =
        (K : ℝ)⁻¹ * (l ^ 2 * Real.pi) := by
      rw [hl2]; field_simp
    rw [heq]
    exact hlvol.trans hlmono
  · apply (div_le_iff₀ hd).mpr
    have heq : (K : ℝ) * (u ^ 2 * Real.pi) =
        (K : ℝ) ^ 2 * (2 * Real.pi / a) * (t - f (e 0)) := by
      rw [hu2]; ring
    exact (humono.trans huvol).trans_eq heq

end PoincareConjecture.RiemannianMetric
