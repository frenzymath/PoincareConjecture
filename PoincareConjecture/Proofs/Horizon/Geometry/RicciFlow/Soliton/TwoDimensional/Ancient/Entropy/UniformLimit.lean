import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Functional
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SurfaceEntropy

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem abs_meanScalar_sub_le {g : RiemannianMetric 2 M} (D : LeviCivitaData g)
    {c e : ℝ} (h : ∀ x, |D.scalarCurvature x - c| ≤ e) :
    |meanScalar D - c| ≤ e := by
  have hi := D.continuous_scalarCurvature.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hv := volume_pos (g := g)
  have hb := norm_integral_le_of_norm_le_const
    (μ := g.volumeMeasure) (f := fun x => D.scalarCurvature x - c)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using h x))
  rw [integral_sub hi (integrable_const c), integral_const, smul_eq_mul,
    integral_scalarCurvature_eq_meanScalar_mul_volume D] at hb
  rw [mul_comm (g.volumeMeasure.real univ) c, ← sub_mul, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hv] at hb
  exact (mul_le_mul_iff_left₀ hv).mp (by simpa only [mul_comm] using hb)

theorem tendsto_meanScalar_of_uniform_scalar
    {g : ℕ → RiemannianMetric 2 M} (D : ∀ k, LeviCivitaData (g k)) {c : ℝ}
    (hR : TendstoUniformly (fun k x => (D k).scalarCurvature x) (fun _ => c) atTop) :
    Tendsto (fun k => meanScalar (D k)) atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro e he
  have h := Metric.tendstoUniformly_iff.mp hR (e / 2) (by positivity)
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  exact (abs_meanScalar_sub_le (D k) (fun x =>
    le_of_lt (by simpa only [Real.dist_eq, abs_sub_comm] using hN k hk x))).trans_lt
    (by linarith)

theorem tendstoUniformly_relativeDensity_of_uniform_scalar
    {g : ℕ → RiemannianMetric 2 M} (D : ∀ k, LeviCivitaData (g k)) {c : ℝ}
    (hc : 0 < c)
    (hR : TendstoUniformly (fun k x => (D k).scalarCurvature x) (fun _ => c) atTop) :
    TendstoUniformly (fun k x => relativeDensity (meanScalar (D k))
      ((D k).scalarCurvature x)) (fun _ => 0) atTop := by
  have hcont : ContinuousAt (fun p : ℝ × ℝ => relativeDensity p.1 p.2) (c, c) := by
    unfold relativeDensity
    exact ((continuous_snd.continuousAt.mul
      ((continuous_snd.continuousAt.div continuous_fst.continuousAt hc.ne').log
        (div_ne_zero hc.ne' hc.ne'))).sub continuous_snd.continuousAt).add
      continuous_fst.continuousAt
  have hm := tendsto_meanScalar_of_uniform_scalar D hR
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  obtain ⟨d, hd, hde⟩ := Metric.continuousAt_iff.mp hcont e he
  filter_upwards [Metric.tendstoUniformly_iff.mp hR d hd,
    (Metric.tendsto_nhds.mp hm) d hd] with k hk hmk x
  have hdist : dist (meanScalar (D k), (D k).scalarCurvature x) (c, c) < d := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hmk, by simpa only [dist_comm] using hk x⟩
  simpa [relativeDensity, hc.ne', dist_comm] using hde hdist

theorem tendsto_scalarEntropy_of_uniform_scalar
    {g : ℕ → RiemannianMetric 2 M} (D : ∀ k, LeviCivitaData (g k)) {c V : ℝ}
    (hc : 0 < c)
    (hR : TendstoUniformly (fun k x => (D k).scalarCurvature x) (fun _ => c) atTop)
    (hV : ∀ᶠ k in atTop, (g k).volumeMeasure.real univ ≤ V) :
    Tendsto (fun k => scalarEntropy (D k)) atTop (𝓝 0) := by
  have hden := tendstoUniformly_relativeDensity_of_uniform_scalar D hc hR
  let B := max V 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  apply Metric.tendsto_nhds.mpr
  intro e he
  have heB : 0 < e / (2 * B) := div_pos he (mul_pos (by norm_num) hB)
  filter_upwards [Metric.tendstoUniformly_iff.mp hden (e / (2 * B)) heB, hV]
    with k hk hkV
  have hb := norm_integral_le_of_norm_le_const (μ := (g k).volumeMeasure)
    (f := fun x => relativeDensity (meanScalar (D k)) ((D k).scalarCurvature x))
    (Filter.Eventually.of_forall (fun x =>
      le_of_lt (by simpa only [dist_zero_right, dist_zero_left] using hk x)))
  rw [dist_zero_right]
  refine hb.trans_lt ?_
  calc
    e / (2 * B) * (g k).volumeMeasure.real univ ≤ e / (2 * B) * B :=
      mul_le_mul_of_nonneg_left (hkV.trans (le_max_left _ _)) heB.le
    _ = e / 2 := by field_simp
    _ < e := by linarith

end PoincareConjecture.SurfaceEntropy
