import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.NullImage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import Mathlib.MeasureTheory.Integral.Indicator

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem volumeMeasure_sphere_eq_zero_of_precompact_ball
    (g : RiemannianMetric n M) (p : M) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    g.volumeMeasure {q | g.edist p q = ENNReal.ofReal r} = 0 := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p hR hcompact
  have hcover := Poincare.VolumeComparison.image_localMinimizingSet_eq_ball
    g p hR hcompact L e hL he0 hed (fun v hv => (hgeo v hv).1)
  have hsub : {q | g.edist p q = ENNReal.ofReal r} ⊆
      e '' Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r := by
    intro q hq
    have hqR : q ∈ g.ball p R := by
      change g.edist p q < ENNReal.ofReal R
      rw [hq]
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR
    rw [← hcover] at hqR
    obtain ⟨v, hv, rfl⟩ := hqR
    refine ⟨v, ?_, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right]
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) hr.le).mp (hv.2.symm.trans hq)
  apply measure_mono_null hsub
  apply g.volumeMeasure_image_eq_zero_of_mdifferentiableAt
  · intro v hv
    apply (he.contMDiffAt (Metric.isOpen_ball.mem_nhds ?_)).mdifferentiableAt
      (by simp)
    rw [Metric.mem_ball, dist_zero_right]
    have hv' : ‖v‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
    rwa [hv']
  · exact Measure.addHaar_sphere_of_ne_zero volume 0 hr.ne'

theorem volumeMeasure_sphere_eq_zero_of_metricComplete
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) (p : M)
    {r : ℝ} (hr : 0 < r) :
    g.volumeMeasure {q | g.edist p q = ENNReal.ofReal r} = 0 :=
  g.volumeMeasure_sphere_eq_zero_of_precompact_ball p hr (lt_add_one r)
    (g.isCompact_closure_ball_of_metricComplete hcomplete p (r + 1))

theorem continuousAt_ball_volume_of_metricComplete
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) (p : M)
    {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun s : ℝ => g.volumeMeasure (g.ball p s)) r := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hball (s : ℝ) : MeasurableSet (g.ball p s) :=
    (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
  have hfinite : g.volumeMeasure (g.ball p (r + 1)) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (subset_closure : g.ball p (r + 1) ⊆ _))
      (g.volumeMeasure_lt_top_of_isCompact
        (g.isCompact_closure_ball_of_metricComplete hcomplete p (r + 1)))).ne
  apply tendsto_measure_of_ae_tendsto_indicator (𝓝 r) (hball r) hball
    (hball (r + 1)) hfinite
  · filter_upwards [eventually_lt_nhds (lt_add_one r)] with s hs q hq
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal hs.le)
  · have hae : ∀ᵐ q ∂g.volumeMeasure, g.edist p q ≠ ENNReal.ofReal r := by
      simpa only [ae_iff, not_not] using
        g.volumeMeasure_sphere_eq_zero_of_metricComplete hcomplete p hr
    filter_upwards [hae] with q hq
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · filter_upwards [(ENNReal.continuous_ofReal.tendsto r).eventually_const_lt hlt]
        with s hs
      exact iff_of_true hs hlt
    · filter_upwards [(ENNReal.continuous_ofReal.tendsto r).eventually_lt_const hgt]
        with s hs
      exact iff_of_false (not_lt_of_ge hs.le) (not_lt_of_ge hgt.le)

theorem continuousAt_ball_volume_toReal_of_metricComplete
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) (p : M)
    {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun s : ℝ => (g.volumeMeasure (g.ball p s)).toReal) r := by
  apply (ENNReal.continuousAt_toReal ?_).comp
    (g.continuousAt_ball_volume_of_metricComplete hcomplete p hr)
  exact (lt_of_le_of_lt (measure_mono (subset_closure : g.ball p r ⊆ _))
    (g.volumeMeasure_lt_top_of_isCompact
      (g.isCompact_closure_ball_of_metricComplete hcomplete p r))).ne

end PoincareConjecture.RiemannianMetric
