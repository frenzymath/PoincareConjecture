import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AngularPaths
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.UniformRayDistance

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology NNReal ENNReal Manifold ContDiff Bundle

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}

theorem rayExtension_dist_eq_twice_of_asymptoticRayDistance_eq_two
    (hc : RayComparison p) (α β : basedMinimizingRays p)
    (hab : asymptoticRayDistance α β = 2) {L : ℝ} (hL : 0 < L) :
    dist (rayExtension α L) (rayExtension β L) = 2 * L := by
  have hlow := asymptoticRayDistance_le_normalized_ray_distance hc α β hL
  rw [hab] at hlow
  have hhigh := dist_triangle (rayExtension α L) p (rayExtension β L)
  have hd (γ : basedMinimizingRays p) : dist p (rayExtension γ L) = L := by
    simpa only [rayExtension_zero, zero_sub, abs_neg, abs_of_pos hL] using
      rayExtension_dist γ (s := 0) le_rfl hL.le
  rw [dist_comm (rayExtension α L) p, hd α, hd β] at hhigh
  have hlower : 2 * L ≤ dist (rayExtension α L) (rayExtension β L) :=
    (le_div_iff₀ hL).mp hlow
  linarith

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem dist_sq_add_dist_sq_le_of_minimizing_midpoint
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (x m y z : M) {L : ℝ} (hL : 0 < L)
    (hxm : g.edist x m = ENNReal.ofReal L)
    (hmy : g.edist m y = ENNReal.ofReal L)
    (hxy : g.edist x y = ENNReal.ofReal (2 * L)) :
    (g.edist z x).toReal ^ 2 + (g.edist z y).toReal ^ 2 ≤
      2 * (g.edist z m).toReal ^ 2 + 2 * L ^ 2 := by
  obtain ⟨γ, hγ, hγ0, hγL, hγ2L, hspeed, hmin⟩ :=
    g.exists_unit_minimizing_geodesic_through hc (by linarith : 0 < 2 * L)
      (show L ∈ Icc (0 : ℝ) (2 * L) from ⟨hL.le, by linarith⟩)
      hxm (by simpa only [show 2 * L - L = L by ring] using hmy) hxy
  have hconc := g.squared_distance_sub_sq_concave D hc hsec z hγ hspeed hmin
  have hh := hconc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) (2 * L) by constructor <;> linarith)
    (show 2 * L ∈ Icc (0 : ℝ) (2 * L) by constructor <;> linarith)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, show (1 / 2 : ℝ) * (2 * L) = L by ring,
    hγ0, hγL, hγ2L, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hh
  nlinarith [hh]

theorem asymptoticRayDistance_sq_add_le_four_of_antipodal
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    ∀ α β ζ : basedMinimizingRays p, asymptoticRayDistance α β = 2 →
      asymptoticRayDistance α ζ ^ 2 + asymptoticRayDistance β ζ ^ 2 ≤ 4 := by
  let := g.toMetricSpace
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  intro α β ζ hab
  apply le_of_tendsto
    (((tendsto_asymptoticRayDistance hc α ζ).pow 2).add
      ((tendsto_asymptoticRayDistance hc β ζ).pow 2))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hd (γ : basedMinimizingRays p) : dist p (rayExtension γ L) = L := by
    simpa only [rayExtension_zero, zero_sub, abs_neg, abs_of_pos hL] using
      rayExtension_dist γ (s := 0) le_rfl hL.le
  have habL := rayExtension_dist_eq_twice_of_asymptoticRayDistance_eq_two hc α β hab hL
  have h := g.dist_sq_add_dist_sq_le_of_minimizing_midpoint D hcomplete hsec
    (rayExtension α L) p (rayExtension β L) (rayExtension ζ L) hL
    (by change EDist.edist (rayExtension α L) p = _; rw [edist_dist, dist_comm, hd])
    (by change EDist.edist p (rayExtension β L) = _; rw [edist_dist, hd])
    (by change EDist.edist (rayExtension α L) (rayExtension β L) = _; rw [edist_dist, habL])
  change dist (rayExtension ζ L) (rayExtension α L) ^ 2 +
    dist (rayExtension ζ L) (rayExtension β L) ^ 2 ≤
      2 * dist (rayExtension ζ L) p ^ 2 + 2 * L ^ 2 at h
  rw [dist_comm (rayExtension ζ L) (rayExtension α L),
    dist_comm (rayExtension ζ L) (rayExtension β L),
    dist_comm (rayExtension ζ L) p, hd ζ] at h
  rw [div_pow, div_pow, ← add_div]
  apply (div_le_iff₀ (sq_pos_of_pos hL)).2
  nlinarith [h]

theorem asymptoticLink_dist_sq_add_le_four_of_antipodal
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∀ x y z : AsymptoticLink p hc, dist x y = 2 →
      dist x z ^ 2 + dist y z ^ 2 ≤ 4 := by
  let := g.toMetricSpace
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  dsimp only
  intro x y z hxy
  obtain ⟨α, rfl⟩ := surjective_asymptoticLinkProjection hc x
  obtain ⟨β, rfl⟩ := surjective_asymptoticLinkProjection hc y
  obtain ⟨ζ, rfl⟩ := surjective_asymptoticLinkProjection hc z
  simp only [dist_asymptoticLinkProjection] at hxy ⊢
  exact g.asymptoticRayDistance_sq_add_le_four_of_antipodal D hcomplete hsec p α β ζ hxy

theorem asymptoticConeUnitSlice_dist_sq_add_le_four_of_antipodal
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∀ x y z : AsymptoticConeUnitSlice p hc, dist x y = 2 →
      dist x z ^ 2 + dist y z ^ 2 ≤ 4 := by
  let := g.toMetricSpace
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  dsimp only
  intro x y z hxy
  let e := asymptoticConeUnitIsometry hc
  simpa only [e.symm.isometry.dist_eq] using
    g.asymptoticLink_dist_sq_add_le_four_of_antipodal D hcomplete hsec p
      (e.symm x) (e.symm y) (e.symm z) (by simpa only [e.symm.isometry.dist_eq] using hxy)

end PoincareConjecture.RiemannianMetric
