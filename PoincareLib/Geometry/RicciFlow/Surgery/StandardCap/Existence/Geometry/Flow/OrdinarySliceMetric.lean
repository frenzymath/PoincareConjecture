import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.OrdinaryProductGeometry
import PoincareLib.Geometry.Riemannian.Homothety.Calculus
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper

/-!
# Actual ordinary slice metric, ball and volume

The retained slice diffeomorphism is a metric homothety of factor one.
Its positive homothety calculus transfers the ordinary ball, calibrated
volume and compact closure to the exact selected spacetime slice.
Source: Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {g : ℝ → RiemannianMetric n M}

/-- The actual slice identification preserves the specified metric
(Proposition 12.13, pp. 304-306). -/
theorem ordinarySlice_metricHomothety (R : OrdinaryProductSpacetimeConclusion g I)
    (t : I.domain) :
    MetricHomothety (g t.val) (R.slices t.val).metricOnPoints (R.sliceIdentification t) 1 := by
  intro x v w
  simpa only [one_mul] using R.sliceMetric_eq t x v w

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  (R : OrdinaryProductSpacetimeConclusion g I) (t : I.domain)
  (C : MetricHomothetyCalculus (g t.val) (R.slices t.val).metricOnPoints
    (R.sliceIdentification t) 1)

include C

/-- Actual metric balls correspond under the selected ordinary slice
identification (Proposition 12.13, pp. 304-306). -/
theorem ordinarySlice_ball (p : M) (r : ℝ) :
    R.sliceIdentification t '' (g t.val).ball p r =
      (R.slices t.val).metricOnPoints.ball (R.sliceIdentification t p) r := by
  simpa only [Real.sqrt_one, one_mul] using C.ball_image p r

/-- The exact calibrated volumes of corresponding balls agree
(Proposition 12.13, pp. 304-306). -/
theorem ordinarySlice_ball_volume (p : M) (r : ℝ) :
    calibratedMetricVolume (R.slices t.val).metricOnPoints
        ((R.slices t.val).metricOnPoints.ball (R.sliceIdentification t p) r) =
      calibratedMetricVolume (g t.val) ((g t.val).ball p r) := by
  rw [← ordinarySlice_ball R t C]
  simpa only [Real.rpow_eq_pow, Real.one_rpow, ENNReal.ofReal_one, one_mul] using
    C.volume_image ((g t.val).ball p r)

/-- Completeness of the ordinary metric gives compact closure of the
corresponding ball in the actual selected slice (Proposition 12.13). -/
theorem ordinarySlice_compact_ball [ConnectedSpace M]
    (hcomplete : MetricComplete (g t.val)) (p : M) (r : ℝ) :
    IsCompact (closure ((R.slices t.val).metricOnPoints.ball (R.sliceIdentification t p) r)) := by
  have h := (Proofs.M09.isCompact_closure_metric_ball (g t.val) hcomplete p r).image
    (R.sliceIdentification t).continuous
  have he : R.sliceIdentification t '' closure ((g t.val).ball p r) =
      closure (R.sliceIdentification t '' (g t.val).ball p r) :=
    (R.sliceIdentification t).toHomeomorph.image_closure _
  rwa [he, ordinarySlice_ball R t C] at h

end PoincareMT.M34
