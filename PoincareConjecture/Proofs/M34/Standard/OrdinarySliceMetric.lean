import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryProductGeometry
import PoincareConjecture.Statements.M13MetricHomothety
import PoincareConjecture.Proofs.M09.RiemannianProper










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {g : ℝ → RiemannianMetric n M}



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



theorem ordinarySlice_ball (p : M) (r : ℝ) :
    R.sliceIdentification t '' (g t.val).ball p r =
      (R.slices t.val).metricOnPoints.ball (R.sliceIdentification t p) r := by
  simpa only [Real.sqrt_one, one_mul] using C.ball_image p r



theorem ordinarySlice_ball_volume (p : M) (r : ℝ) :
    calibratedMetricVolume (R.slices t.val).metricOnPoints
        ((R.slices t.val).metricOnPoints.ball (R.sliceIdentification t p) r) =
      calibratedMetricVolume (g t.val) ((g t.val).ball p r) := by
  rw [← ordinarySlice_ball R t C]
  simpa only [Real.rpow_eq_pow, Real.one_rpow, ENNReal.ofReal_one, one_mul] using
    C.volume_image ((g t.val).ball p r)



theorem ordinarySlice_compact_ball [ConnectedSpace M]
    (hcomplete : MetricComplete (g t.val)) (p : M) (r : ℝ) :
    IsCompact (closure ((R.slices t.val).metricOnPoints.ball (R.sliceIdentification t p) r)) := by
  have h := (Proofs.M09.isCompact_closure_metric_ball (g t.val) hcomplete p r).image
    (R.sliceIdentification t).continuous
  have he : R.sliceIdentification t '' closure ((g t.val).ball p r) =
      closure (R.sliceIdentification t '' (g t.val).ball p r) :=
    (R.sliceIdentification t).toHomeomorph.image_closure _
  rwa [he, ordinarySlice_ball R t C] at h

end PoincareConjecture.M34
