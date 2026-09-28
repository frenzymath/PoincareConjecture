import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeDensity
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeDomain
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

universe u

namespace PoincareConjecture.M28

open tube

private abbrev E := EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



theorem normalized_neck_chart_edist_le (N : EpsilonNeck g)
    (hscale : N.scale = 1) (hsmall : N.epsilon ≤ (1 / 200 : ℝ))
    {S : ℝ} (hS : S ≤ N.epsilon⁻¹ / 16) (q : UnitTwoSphere) {s : ℝ}
    (hs : |s| ≤ 2 * S) {x y : E}
    (hx : x ∈ Metric.closedBall 0 1) (hy : y ∈ Metric.closedBall 0 1) :
    g.edist (cylinderNeckChart N q s x) (cylinderNeckChart N q s y) ≤
      ENNReal.ofReal 4 * edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdomain := normalized_neck_unit_ball_subset_domain N hsmall hS q hs
  have hsmooth (z : E) (hz : z ∈ Metric.closedBall (0 : E) 1) :
      ContMDiffAt (𝓡 3) (𝓡 3) 1 (cylinderNeckChart N q s) z :=
    ((contMDiffOn_cylinderNeckChart N q s).contMDiffAt
      ((isOpen_cylinderNeckChartDomain N q s).mem_nhds (hdomain hz))).of_le (by simp)
  have hbound (z : E) (hz : z ∈ Metric.closedBall (0 : E) 1) :
      ‖mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) z‖ₑ ≤ (4 : ℝ≥0) := by
    rw [← ofReal_norm, ENNReal.ofReal_le_coe]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    change g.tangentNorm (cylinderNeckChart N q s z)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) z v) ≤ (4 : ℝ) * ‖v‖
    exact (normalized_neck_chart_speed_bounds N hscale q s (hdomain hz)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) v).2
  simpa only [RiemannianMetric.edist, ENNReal.coe_ofNat, ENNReal.ofReal_ofNat] using
    Poincare.riemannianEDist_le_mul_edist_of_convex
      (convex_closedBall (0 : E) 1) hsmooth hbound hx hy



theorem normalized_neck_chart_ball_subset (N : EpsilonNeck g)
    (hscale : N.scale = 1) (hsmall : N.epsilon ≤ (1 / 200 : ℝ))
    {S : ℝ} (hS : S ≤ N.epsilon⁻¹ / 16) (q : UnitTwoSphere) {s : ℝ}
    (hs : |s| ≤ 2 * S) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) :
    cylinderNeckChart N q s '' Metric.ball (0 : E) (δ / 4) ⊆
      g.ball (cylinderNeckChart N q s 0) δ := by
  rintro _ ⟨x, hx, rfl⟩
  have hxnorm : ‖x‖ < δ / 4 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hxunit : x ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hdist := normalized_neck_chart_edist_le N hscale hsmall hS q hs
    (by simp : (0 : E) ∈ Metric.closedBall 0 1) hxunit
  apply hdist.trans_lt
  rw [edist_eq_enorm_sub, zero_sub, enorm_neg, ← ofReal_norm,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
  linarith




theorem normalized_neck_chart_image_volume_bounds
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (N : EpsilonNeck g) (hscale : N.scale = 1)
    (hsmall : N.epsilon ≤ (1 / 200 : ℝ)) {S : ℝ}
    (hS : S ≤ N.epsilon⁻¹ / 16) (q : UnitTwoSphere) {s : ℝ}
    (hs : |s| ≤ 2 * S) {U : Set E} (hU : MeasurableSet U)
    (hUunit : U ⊆ Metric.closedBall 0 1) :
    ENNReal.ofReal (1 / 48 : ℝ) * volume U ≤
        g.volumeMeasure (cylinderNeckChart N q s '' U) ∧
      g.volumeMeasure (cylinderNeckChart N q s '' U) ≤
        ENNReal.ofReal 384 * volume U := by
  have hdomain := normalized_neck_unit_ball_subset_domain N hsmall hS q hs
  have hUe : U ⊆ (neckVolumeChart N q s).source := by
    rw [neckVolumeChart_source]
    exact hUunit.trans hdomain
  have heq := g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity
    (neckVolumeChart N q s) (neckVolumeChart_smooth N q s)
    (neckVolumeChart_symm_smooth N q s) hU hUe
  change g.volumeMeasure (cylinderNeckChart N q s '' U) =
    ∫⁻ x in U, ENNReal.ofReal (g.pullbackVolumeDensity (cylinderNeckChart N q s) x) at heq
  rw [heq]
  have hdensity (x : E) (hx : x ∈ U) :=
    normalized_neck_chart_density_bounds N hscale q s (hdomain (hUunit hx))
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hUunit hx)
  constructor
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hU (fun x hx => ENNReal.ofReal_le_ofReal (hdensity x hx).1)
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hU (fun x hx => ENNReal.ofReal_le_ofReal (hdensity x hx).2)

end PoincareConjecture.M28
