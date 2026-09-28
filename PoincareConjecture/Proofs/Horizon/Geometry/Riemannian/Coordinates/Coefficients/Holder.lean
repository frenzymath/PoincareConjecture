import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Dual
import Mathlib.Analysis.Calculus.MeanValue









set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))



lemma norm_coefficients_sub_le_sqrt {R H : ℝ} (hH : 0 ≤ H)
    (hderiv : ∀ z ∈ Metric.ball 0 R, ‖fderiv ℝ g.euclideanCoefficients z‖ ≤ H)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R)
    (hy : y ∈ Metric.ball 0 R) :
    ‖g.euclideanCoefficients x - g.euclideanCoefficients y‖ ≤
      (H * Real.sqrt (2 * R)) * Real.sqrt ‖x - y‖ := by
  have hLip := (convex_ball (0 : EuclideanSpace ℝ (Fin n)) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ (g.contDiffAt_euclideanCoefficients z).differentiableAt (by simp))
    hderiv hy hx
  have hdiam : ‖x - y‖ ≤ 2 * R := by
    have hx' : ‖x‖ < R := mem_ball_zero_iff.mp hx
    have hy' : ‖y‖ < R := mem_ball_zero_iff.mp hy
    exact (norm_sub_le x y).trans (by linarith)
  have hsqrt := Real.sqrt_le_sqrt hdiam
  have hdist : ‖x - y‖ ≤ Real.sqrt (2 * R) * Real.sqrt ‖x - y‖ := by
    calc
      _ = Real.sqrt ‖x - y‖ * Real.sqrt ‖x - y‖ :=
        (Real.mul_self_sqrt (norm_nonneg _)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
  calc
    _ ≤ H * ‖x - y‖ := hLip
    _ ≤ H * (Real.sqrt (2 * R) * Real.sqrt ‖x - y‖) :=
      mul_le_mul_of_nonneg_left hdist hH
    _ = _ := by ring



lemma abs_inverseCoefficients_sub_le_sqrt {a R H : ℝ} (ha : 0 < a) (hH : 0 ≤ H)
    (hell : ∀ z ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.inner z v v)
    (hderiv : ∀ z ∈ Metric.ball 0 R, ‖fderiv ℝ g.euclideanCoefficients z‖ ≤ H)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R)
    (hy : y ∈ Metric.ball 0 R) (i j : Fin n) :
    |g.inverseCoefficients x i j - g.inverseCoefficients y i j| ≤
      ((H * Real.sqrt (2 * R)) / a ^ 2) * Real.sqrt ‖x - y‖ := by
  exact g.abs_inverseCoefficients_sub_le x y ha (hell x hx) (hell y hy)
    (g.norm_coefficients_sub_le_sqrt hH hderiv hx hy) i j

end PoincareConjecture.RiemannianMetric
