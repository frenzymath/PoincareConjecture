import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Precompact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

theorem modelVolume_mono_radius (n : ℕ) {κ r R : ℝ}
    (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hrR : r ≤ R) :
    modelVolume n κ r ≤ modelVolume n κ R := by
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_nonneg n))
  apply intervalIntegral.integral_mono_interval le_rfl hr hrR _
    (intervalIntegrable_modelS_pow n κ 0 R)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact pow_nonneg (modelS_nonneg hκ ht.1.le) _

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

theorem volumeMeasure_real_ball_le_modelVolume_of_ricci_lower_bound
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) (hcomplete : MetricComplete g) (D : LeviCivitaData g)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v)
    {r : ℝ} (hr : 0 < r) :
    g.volumeMeasure.real (g.ball p r) ≤ modelVolume n κ r := by
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  let : SecondCountableTopology M := g.secondCountableTopology
  have hcompact : IsCompact (closure (g.ball p (r + 1))) := by
    rw [← g.toMetricSpace_ball]
    exact (isCompact_closedBall p (r + 1)).of_isClosed_subset
      isClosed_closure Metric.closure_ball_subset_closedBall
  obtain ⟨hmono, hlim⟩ := g.relativeVolumeComparison_of_precompact_ball p hn
    (show 0 < r + 1 by linarith) hκ hcompact D (fun x _ => hRic x)
  have hratio : g.volumeMeasure (g.ball p r) / ENNReal.ofReal (modelVolume n κ r) ≤ 1 := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    exact hmono ⟨hs.1, by linarith [hs.2]⟩ ⟨hr, by linarith⟩ hs.2.le
  have hpos := modelVolume_pos hn hκ hr
  have hvol := mul_le_mul' hratio (le_refl (ENNReal.ofReal (modelVolume n κ r)))
  rw [ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne'
    ENNReal.ofReal_ne_top, one_mul] at hvol
  simpa only [Measure.real, ENNReal.toReal_ofReal hpos.le] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol

theorem volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    (hcomplete : MetricComplete g) (D : LeviCivitaData g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    {r : ℝ} (hr : 0 < r) :
    g.volumeMeasure.real (g.ball p r) ≤ modelVolume n 1 r := by
  exact g.volumeMeasure_real_ball_le_modelVolume_of_ricci_lower_bound p hn (by norm_num)
    hcomplete D
    (fun x v => D.ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound
      x 1 (hsec x) v) hr

end PoincareConjecture.RiemannianMetric
