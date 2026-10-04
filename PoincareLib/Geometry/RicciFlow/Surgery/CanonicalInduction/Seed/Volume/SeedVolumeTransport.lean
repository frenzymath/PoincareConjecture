import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Image.SeedImageBalls

/-!
# Volume transfer through the actual seed chart

The inverse length barrier constructs target-ball coverage; the actual
local volume comparison then transfers its density to the source ball.
Source: MT Theorems 12.28-12.29 and Uniform Seed, pp. 323-325 and 392-393.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareMT.Proofs.M47

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]
  [T3Space X] [T3Space Y] [SecondCountableTopology X]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- Actual quadratic comparisons and a compact source buffer transfer
the target inner-ball volume to the source without a coverage premise.
The fixed factor is independent of event count; MT pp. 392-393. -/
theorem seed_target_ball_volume_le_source
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞)
    (hlower : ∀ x ∈ C.source, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ 4 * h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x v))
    (hupper : ∀ x ∈ C.source, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x v) ≤ 4 * g.inner x v v)
    (p : X) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure (g.ball p r)))
    (hsource : closure (g.ball p r) ⊆ C.source) :
    calibratedMetricVolume h (h.ball (C p) (r / 2)) ≤
      8 * calibratedMetricVolume g (g.ball p r) := by
  have hcover := seed_ball_subset_image g h C hlower p hr hcompact hsource
  have hnorm : ∀ x ∈ C.source, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (C x) (mfderiv (𝓡 3) (𝓡 3) C x v) ≤ 2 * g.tangentNorm x v := by
    intro x hx v
    unfold RiemannianMetric.tangentNorm
    apply (Real.sqrt_le_sqrt (hupper x hx v)).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hfour]
  have hopen : IsOpen (g.ball p r) :=
    isOpen_Iio.preimage ((M36.metric_edist_continuous g).comp
      (continuous_const.prodMk continuous_id))
  have hvol := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le g h
    C.toOpenPartialHomeomorph (C.contMDiffOn.of_le (by simp))
    (by norm_num : (0 : ℝ) < 2) hnorm hopen.measurableSet (subset_closure.trans hsource)
  have h := (measure_mono hcover).trans hvol
  norm_num at h ⊢
  exact h

/-- A target inner-ball density becomes a fixed source-ball density
through the actual chart. All geometric inputs are discharged by the
retained search bounds; Uniform Seed, pp. 392-393. -/
theorem seed_volume_density_transfer
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞)
    (hlower : ∀ x ∈ C.source, ∀ v : TangentSpace (𝓡 3) x,
      g.inner x v v ≤ 4 * h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x v))
    (hupper : ∀ x ∈ C.source, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (C x) (mfderiv (𝓡 3) (𝓡 3) C x v)
        (mfderiv (𝓡 3) (𝓡 3) C x v) ≤ 4 * g.inner x v v)
    (p : X) {r k : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure (g.ball p r)))
    (hsource : closure (g.ball p r) ⊆ C.source)
    (hvolume : ENNReal.ofReal (k * (r / 2) ^ 3) ≤
      calibratedMetricVolume h (h.ball (C p) (r / 2))) :
    ENNReal.ofReal ((k / 64) * r ^ 3) ≤ calibratedMetricVolume g (g.ball p r) := by
  have h := hvolume.trans (seed_target_ball_volume_le_source g h C hlower hupper
    p hr hcompact hsource)
  calc
    ENNReal.ofReal ((k / 64) * r ^ 3) =
        ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (k * (r / 2) ^ 3) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (1 / 8 : ℝ) * (8 * calibratedMetricVolume g (g.ball p r)) :=
      mul_le_mul_right h _
    _ = calibratedMetricVolume g (g.ball p r) := by
      rw [← mul_assoc]
      have hcancel : ENNReal.ofReal (1 / 8 : ℝ) * 8 = 1 := by
        rw [← show ENNReal.ofReal (8 : ℝ) = (8 : ℝ≥0∞) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
        norm_num
      rw [hcancel, one_mul]

end PoincareMT.Proofs.M47
