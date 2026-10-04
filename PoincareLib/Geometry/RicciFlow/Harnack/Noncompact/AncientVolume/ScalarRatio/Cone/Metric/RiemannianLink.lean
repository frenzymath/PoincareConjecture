import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Link
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MetricComparison
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MinimizingRay
import PoincareLib.Geometry.Riemannian.Compactness.IntrinsicMetric

/-!
# The asymptotic link of a complete nonnegatively curved manifold

Intrinsic Toponogov comparison supplies ray comparison. Completeness gives
compactness of the based rays, and noncompactness gives a ray from every base
point. Thus the actual asymptotic metric link is nonempty and compact.

Reference: Kleiner--Lott (corrected 2013), Theorem 41.2, Case 2, p. 2677,
and Appendix G, p. 2852.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Restrict an intrinsic unit-speed minimizing ray to nonnegative time. -/
def basedMinimizingRayOfEdist (g : RiemannianMetric n M) {p : M}
    (ray : ℝ → M) (hzero : ray 0 = p)
    (hmin : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
      g.edist (ray s) (ray t) = ENNReal.ofReal |s - t|) :
    letI := g.toMetricSpace
    basedMinimizingRays p := by
  letI := g.toMetricSpace
  refine ⟨fun t => ray t, hzero, Isometry.of_dist_eq ?_⟩
  intro s t
  change (g.edist (ray s) (ray t)).toReal = |(s : ℝ) - (t : ℝ)|
  rw [hmin s s.2 t t.2, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem rayExtension_basedMinimizingRayOfEdist (g : RiemannianMetric n M) {p : M}
    (ray : ℝ → M) (hzero : ray 0 = p)
    (hmin : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
      g.edist (ray s) (ray t) = ENNReal.ofReal |s - t|)
    {t : ℝ} (ht : 0 ≤ t) :
    letI := g.toMetricSpace
    rayExtension (g.basedMinimizingRayOfEdist ray hzero hmin) t = ray t := by
  simp only [rayExtension, basedMinimizingRayOfEdist, Real.coe_toNNReal t ht]

/-- The complete manifold's sectional curvature supplies all comparison
inequalities used in the asymptotic metric construction. -/
theorem rayComparison_of_metricComplete
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    RayComparison p := by
  let := g.toMetricSpace
  intro γ η a b ha hb s hs t ht
  have hmin (ζ : basedMinimizingRays p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
      g.edist (rayExtension ζ u) (rayExtension ζ v) = ENNReal.ofReal |u - v| := by
    change EDist.edist (rayExtension ζ u) (rayExtension ζ v) = _
    rw [edist_dist, rayExtension_dist ζ hu hv]
  exact g.toponogov_corresponding_side_of_edist_segments D hc hsec ha hb
    (rayExtension_zero γ) (rayExtension_zero η)
    (fun u hu v hv => hmin γ hu.1 hv.1)
    (fun u hu v hv => hmin η hu.1 hv.1) s hs t ht

theorem nonempty_basedMinimizingRays [NoncompactSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) :
    letI := g.toMetricSpace
    Nonempty (basedMinimizingRays p) := by
  obtain ⟨ray, hzero, hmin⟩ := g.exists_minimizing_ray_of_metricComplete hc p
  exact ⟨g.basedMinimizingRayOfEdist ray hzero hmin⟩

/-- The actual link is nonempty and compact under the geometric source
hypotheses; neither ray comparison nor link compactness is an extra input. -/
theorem asymptoticLink_nonempty_compact [NoncompactSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    Nonempty (AsymptoticLink p hcomparison) ∧ CompactSpace (AsymptoticLink p hcomparison) := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  obtain ⟨γ⟩ := g.nonempty_basedMinimizingRays hc p
  exact ⟨⟨asymptoticLinkProjection (g.rayComparison_of_metricComplete D hc hsec p) γ⟩,
    inferInstance⟩

end PoincareMT.RiemannianMetric
