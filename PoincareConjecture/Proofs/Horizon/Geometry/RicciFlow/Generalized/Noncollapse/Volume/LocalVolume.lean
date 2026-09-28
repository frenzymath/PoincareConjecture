import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Noncollapse.Volume.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.CompactImage
















set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.Generalized.Noncollapse

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem calibratedMetricVolume_eq_volumeMeasure (g : RiemannianMetric n M) :
    calibratedMetricVolume g = g.volumeMeasure :=
  calibratedMetricVolume_eq_euclideanHausdorff g



theorem calibratedMetricVolume_lt_top_of_isCompact (g : RiemannianMetric n M)
    {s : Set M} (hs : IsCompact s) : calibratedMetricVolume g s < ⊤ := by
  rw [calibratedMetricVolume_eq_volumeMeasure]
  exact g.volumeMeasure_lt_top_of_isCompact hs



theorem calibratedMetricVolume_ball_lt_top_of_precompact (g : RiemannianMetric n M)
    (x : M) (r : ℝ) (hcompact : IsCompact (closure (g.ball x r))) :
    calibratedMetricVolume g (g.ball x r) < ⊤ :=
  (measure_mono subset_closure).trans_lt
    (calibratedMetricVolume_lt_top_of_isCompact g hcompact)



theorem calibratedMetricVolume_ball_pos (g : RiemannianMetric n M)
    (x : M) {r : ℝ} (hr : 0 < r) : 0 < calibratedMetricVolume g (g.ball x r) := by
  rw [calibratedMetricVolume_eq_volumeMeasure]
  exact g.volumeMeasure_ball_pos x hr




theorem calibratedMetricVolume_image_le_of_tangentNorm_le_on_compact
    {N : Type v} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    [MeasurableSpace N] [BorelSpace N] [T3Space N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {f : M → N} {U s : Set M} (hU : IsOpen U) (hs : IsCompact s) (hsU : s ⊆ U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 f U) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ w : TangentSpace (𝓡 n) x,
      h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w) ≤ C * g.tangentNorm x w) :
    calibratedMetricVolume h (f '' s) ≤
      ENNReal.ofReal C ^ n * calibratedMetricVolume g s := by
  simpa only [calibratedMetricVolume_eq_volumeMeasure] using
    g.volumeMeasure_image_le_of_tangentNorm_le_on_compact h hU hs hsU hf hC hbound

end PoincareConjecture.Generalized.Noncollapse
