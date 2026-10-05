import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Volume.Calibration
import PoincareLib.Geometry.Riemannian.Measure.Balls
import PoincareLib.Geometry.Riemannian.Measure.CompactImage

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Thm1_34_LocalVolume.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# Local volume facts in the frozen calibration

Morgan-Tian Theorems 1.33-1.34, p. 19, and Claim 8.8, pp. 174-175.
The M06 implementation supplies local intrinsic-volume results. The exact
calibration bridge transfers them to the measure used by the M15 contract.
The permitted lower import routes and the geometric application are recorded
in `references/ricci-flow/mapher/noncollapse/derivations/2026-09-20-local-volume-transport.md`
and `proof-work/tasks/M15/reports/2026-09-20-lower-geometry-survey.md`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareMT.Generalized.Noncollapse

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

/-- The exact volume convention used to apply Theorem 1.34, p. 19,
and Claim 8.8, p. 174, through the permitted M06 helpers. -/
theorem calibratedMetricVolume_eq_volumeMeasure (g : RiemannianMetric n M) :
    calibratedMetricVolume g = g.volumeMeasure :=
  calibratedMetricVolume_eq_euclideanHausdorff g

/-- Compact sets have finite calibrated volume, as needed in the local
volume comparison of Claim 8.8, pp. 174-175. -/
theorem calibratedMetricVolume_lt_top_of_isCompact (g : RiemannianMetric n M)
    {s : Set M} (hs : IsCompact s) : calibratedMetricVolume g s < ⊤ := by
  rw [calibratedMetricVolume_eq_volumeMeasure]
  exact g.volumeMeasure_lt_top_of_isCompact hs

/-- Compact closure suffices for finite ball volume in Theorem 8.1,
p. 169; completeness is unnecessary. -/
theorem calibratedMetricVolume_ball_lt_top_of_precompact (g : RiemannianMetric n M)
    (x : M) (r : ℝ) (hcompact : IsCompact (closure (g.ball x r))) :
    calibratedMetricVolume g (g.ball x r) < ⊤ :=
  (measure_mono subset_closure).trans_lt
    (calibratedMetricVolume_lt_top_of_isCompact g hcompact)

/-- Positive-radius balls have positive calibrated volume. This justifies
the volume ratio in Proposition 8.2, p. 170. -/
theorem calibratedMetricVolume_ball_pos (g : RiemannianMetric n M)
    (x : M) {r : ℝ} (hr : 0 < r) : 0 < calibratedMetricVolume g (g.ball x r) := by
  rw [calibratedMetricVolume_eq_volumeMeasure]
  exact g.volumeMeasure_ball_pos x hr

/-- A local differential norm bound controls the calibrated volume of a
compact image. This is the local measure comparison used in Claim 8.8,
pp. 174-175, without a global identification of intrinsic distances. -/
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

end PoincareMT.Generalized.Noncollapse
