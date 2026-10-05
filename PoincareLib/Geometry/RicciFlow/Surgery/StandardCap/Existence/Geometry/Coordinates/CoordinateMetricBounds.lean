import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.CoordinateVolumeBounds
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Analysis.Distance.SegmentDistance
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Analysis.Distance.SegmentDistance

/-!
# Coordinate bounds for actual metric balls

A bounded pullback form controls tangent lengths, and M10's affine-segment
comparison places small coordinate balls inside the actual metric balls.
Source: Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal NNReal

namespace PoincareMT.M34

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A bound for the actual pullback bilinear form bounds the differential
in the selected metric norm (Proposition 12.13, pp. 304-306). -/
theorem tangentNorm_mfderiv_le_of_pullbackMetricForm_norm_le
    (g : RiemannianMetric n M) (f : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) {b : ℝ} (hb : 0 ≤ b)
    (hB : ‖M10.pullbackMetricForm g f x‖ ≤ b) (v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ Real.sqrt b * ‖v‖ := by
  change Real.sqrt (M10.pullbackMetricForm g f x v v) ≤ _
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_⟩
  calc
    _ ≤ ‖M10.pullbackMetricForm g f x v v‖ := le_abs_self _
    _ ≤ ‖M10.pullbackMetricForm g f x‖ * ‖v‖ * ‖v‖ :=
      (M10.pullbackMetricForm g f x).le_opNorm₂ v v
    _ ≤ b * ‖v‖ * ‖v‖ := by gcongr
    _ = (Real.sqrt b * ‖v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hb]
      ring

/-- A uniform differential bound places coordinate balls in actual metric
balls, using a fixed larger smooth chart domain (Proposition 12.13). -/
theorem coordinate_ball_subset_metric_ball (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) {delta c r : ℝ}
    (hdelta : 0 < delta) (hc : 0 < c) (hr : 0 < r) (hrdelta : r ≤ delta)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 f (Metric.ball 0 (2 * delta)))
    (hbound : ∀ x ∈ Metric.ball 0 (2 * delta), ∀ v : EuclideanSpace ℝ (Fin n),
      g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ c * ‖v‖) :
    f '' Metric.ball 0 r ⊆ g.ball (f 0) (c * r) := by
  let C : ℝ≥0 := ⟨c, hc.le⟩
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal c :=
    (ENNReal.ofReal_eq_coe_nnreal hc.le).symm
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ Metric.ball 0 (2 * delta) :=
    Metric.ball_subset_ball (by linarith) hz
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 (2 * delta) := by
    simpa only [Metric.mem_ball, dist_self] using (show 0 < 2 * delta by positivity)
  have hd := M10.riemannianEDist_le_of_differential_bound g (convex_ball _ _) Metric.isOpen_ball
    hf (C := C) hbound hzero hz'
  rw [hC, edist_dist, dist_zero_left] at hd
  change g.edist (f 0) (f z) < ENNReal.ofReal (c * r)
  rw [ENNReal.ofReal_mul hc.le]
  apply hd.trans_lt
  apply ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top
  apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
  simpa only [Metric.mem_ball, dist_zero_right] using hz

end PoincareMT.M34
