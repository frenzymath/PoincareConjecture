import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.LocalBall
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Model
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.RatioLimit

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem euclidean_ball_volume_eq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) =
      ENNReal.ofReal (euclideanUnitBallVolume n * r ^ n) := by
  rw [Measure.addHaar_ball_of_pos volume _ hr]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [ENNReal.ofReal_mul (euclideanUnitBallVolume_nonneg n),
    euclideanUnitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  exact mul_comm _ _

theorem tendsto_volumeMeasure_ball_div_euclidean
    (g : RiemannianMetric n M) (p : M) :
    Tendsto (fun r : ℝ => g.volumeMeasure (g.ball p r) /
      ENNReal.ofReal (euclideanUnitBallVolume n * r ^ n))
      (𝓝[>] 0) (𝓝 1) := by
  have h := Poincare.VolumeComparison.tendsto_div_one_of_eventually_bounds
    (a := fun r : ℝ => g.volumeMeasure (g.ball p r))
    (b := fun r : ℝ => volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r))
    (l := 𝓝[>] 0) (2 * n) ?_ (fun K hK => g.eventually_volumeMeasure_ball_bounds p hK)
  · apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [euclidean_ball_volume_eq n hr]
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact ⟨(Metric.measure_ball_pos volume _ hr).ne', measure_ball_lt_top.ne⟩

theorem tendsto_volumeMeasure_ball_div_modelVolume
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun r : ℝ => g.volumeMeasure (g.ball p r) /
      ENNReal.ofReal (modelVolume n κ r)) (𝓝[>] 0) (𝓝 1) := by
  have hmodel : Tendsto (fun r : ℝ => ENNReal.ofReal (modelVolume n κ r) /
      ENNReal.ofReal (euclideanUnitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_modelVolume_div_euclidean hn hκ)
    simp only [ENNReal.ofReal_one] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ENNReal.ofReal_div_of_pos
      (mul_pos (euclideanUnitBallVolume_pos n) (pow_pos hr n))
  have h := ENNReal.Tendsto.div (g.tendsto_volumeMeasure_ball_div_euclidean p)
    (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ 0)) hmodel
    (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ ⊤))
  simp only [ENNReal.div_self (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hb0 : ENNReal.ofReal (euclideanUnitBallVolume n * r ^ n) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (mul_pos (euclideanUnitBallVolume_pos n) (pow_pos hr n))).ne'
  simpa only [div_eq_mul_inv] using
    ENNReal.mul_div_mul_right (g.volumeMeasure (g.ball p r))
      (ENNReal.ofReal (modelVolume n κ r))
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top) (ENNReal.inv_ne_top.mpr hb0)

end PoincareConjecture.RiemannianMetric
