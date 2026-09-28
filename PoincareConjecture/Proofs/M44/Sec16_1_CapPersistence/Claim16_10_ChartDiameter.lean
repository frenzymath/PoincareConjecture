import PoincareConjecture.Proofs.M36.MetricComparison
import PoincareConjecture.Proofs.M36.StandardBalls
import PoincareConjecture.Proofs.M01.NormalizationScaling
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Euclidean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem euclidean_lineMap_pathELength (x y : E) :
    (RiemannianMetric.euclideanMetric 3).pathELength
      (ContinuousAffineMap.lineMap (R := ℝ) x y) 0 1 = edist x y := by
  rw [M36.pathELength_eq_integral_speed _
    (contMDiff_iff_contDiff.mpr (ContinuousAffineMap.contDiff _)) zero_le_one]
  have hspeed (t : ℝ) : M36.metricPathSpeed (RiemannianMetric.euclideanMetric 3)
      (ContinuousAffineMap.lineMap (R := ℝ) x y) t = ‖y - x‖ := by
    have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (ContinuousAffineMap.lineMap (R := ℝ) x y) t =
        (ContinuousLinearMap.id ℝ ℝ).smulRight (y - x) := by
      rw [mfderiv_eq_fderiv, ContinuousAffineMap.fderiv]
      apply ContinuousLinearMap.ext
      intro a
      change (AffineMap.lineMap (k := ℝ) x y).linear a = a • (y - x)
      rw [AffineMap.lineMap_linear]
      rfl
    rw [M36.metricPathSpeed, RiemannianMetric.euclideanMetric_tangentNorm]
    rw [hd]
    change ‖(1 : ℝ) • (y - x)‖ = ‖y - x‖
    rw [one_smul]
  simp only [hspeed, intervalIntegral.integral_const, sub_zero, one_smul,
    edist_dist, dist_eq_norm, norm_sub_rev]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]

theorem edist_image_le_of_convex_quadratic
    (g : RiemannianMetric 3 M) {f : E → M} {U : Set E}
    (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) {L : ℝ} (hL : 0 < L)
    (hmetric : ∀ x ∈ U, ∀ v : E, g.pullbackCoefficients f x v v ≤ L ^ 2 * ‖v‖ ^ 2)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    g.edist (f x) (f y) ≤ ENNReal.ofReal (L * ‖x - y‖) := by
  let gamma := ContinuousAffineMap.lineMap (R := ℝ) x y
  let gE := m01RescaledMetric (RiemannianMetric.euclideanMetric 3) (L ^ 2)
    (sq_pos_of_pos hL)
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mpr gamma.contDiff.contDiffOn
  have hmaps : gamma '' Icc 0 1 ⊆ U := by
    simpa only [gamma, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap] using
      hconvex.segment_subset hx hy
  have hbound := M36.edist_comp_le_pathELength_of_pullback_bound gE g
    (fun z hz => hf.contMDiffAt (hU.mem_nhds hz))
    (fun z hz v => by
      change g.pullbackCoefficients f z v v ≤ L ^ 2 * @inner ℝ E _ v v
      simpa only [real_inner_self_eq_norm_sq] using hmetric z hz v)
    zero_le_one hgamma hmaps
  rw [show gamma 0 = x by simp [gamma, ContinuousAffineMap.coe_lineMap_eq],
    show gamma 1 = y by simp [gamma, ContinuousAffineMap.coe_lineMap_eq],
    m01RescaledMetric_pathELength, euclidean_lineMap_pathELength,
    Real.sqrt_sq hL.le, edist_dist, dist_eq_norm, ← ENNReal.ofReal_mul hL.le] at hbound
  exact hbound

theorem standard_ball_image_diameter_lt
    (g0 : StandardInitialMetric) (g : RiemannianMetric 3 M)
    {R h L : ℝ} (hR : 0 < R) (hh : 0 < h) (hL : 0 < L)
    {f : E → M} (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (g0.metric.ball 0 R))
    (hmetric : ∀ x ∈ g0.metric.ball 0 R, ∀ v : E,
      g.pullbackCoefficients f x v v ≤ (h * L) ^ 2 * ‖v‖ ^ 2)
    {x y : E} (hx : x ∈ g0.metric.ball 0 R) (hy : y ∈ g0.metric.ball 0 R) :
    g.edist (f x) (f y) < ENNReal.ofReal
      (h * (2 * L * M36.radialEuclideanRadius g0 R)) := by
  have hball := M36.standard_ball_eq_euclidean g0 hR
  have hdist : ‖x - y‖ < 2 * M36.radialEuclideanRadius g0 R := by
    rw [hball, Metric.mem_ball, dist_zero_right] at hx hy
    exact (norm_sub_le x y).trans_lt (by linarith)
  have hbound := edist_image_le_of_convex_quadratic g (hball ▸ Metric.isOpen_ball)
    (hball ▸ convex_ball (0 : E) (M36.radialEuclideanRadius g0 R))
    hf (mul_pos hh hL) hmetric hx hy
  apply hbound.trans_lt
  apply ENNReal.ofReal_lt_ofReal_iff (by
    have hrho := (M36.radialEuclideanRadius_pos_iff g0 R).mpr hR
    positivity) |>.mpr
  nlinarith only [mul_lt_mul_of_pos_left hdist (mul_pos hh hL)]

end PoincareConjecture.M44
