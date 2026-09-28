import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring













set_option autoImplicit false

open Set

namespace Poincare.Parabolic.Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem norm_fderiv_le_of_hessian_bound
    {f : E → F} {s : Set E} {B K ε : ℝ}
    (hs : Convex ℝ s) (hB : 0 ≤ B) (hK : 0 ≤ K) (hε : 0 < ε)
    (hf : ∀ y ∈ s, DifferentiableAt ℝ f y)
    (hdf : ∀ y ∈ s, DifferentiableAt ℝ (fderiv ℝ f) y)
    (hvalue : ∀ y ∈ s, ‖f y‖ ≤ B)
    (hhessian : ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ K)
    {x : E} (hx : x ∈ s)
    (hstep : ∀ v : E, ‖v‖ = 1 → x + ε • v ∈ s) :
    ‖fderiv ℝ f x‖ ≤ 2 * B / ε + K * ε := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm
  · positivity
  intro v hv
  let y := x + ε • v
  have hy : y ∈ s := hstep v hv
  have hstepEq : y - x = ε • v := by simp [y]
  have hstepNorm : ‖y - x‖ = ε := by
    rw [hstepEq, norm_smul, Real.norm_of_nonneg hε.le, hv, mul_one]
  have hderivBound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ K * ε := by
    intro z hz
    calc
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ K * ‖z - x‖ :=
        hs.norm_image_sub_le_of_norm_fderiv_le hdf hhessian hx
          (hs.segment_subset hx hy hz)
      _ ≤ K * ε := mul_le_mul_of_nonneg_left
        (by simpa [hstepNorm] using norm_sub_le_of_mem_segment hz) hK
  have htaylor := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f x)
    (fun z hz => hf z (hs.segment_subset hx hy hz)) hderivBound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hvalues : ‖f y - f x‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by linarith [hvalue y hy, hvalue x hx])
  have hnorm := norm_le_norm_add_norm_sub (f y - f x) (fderiv ℝ f x (y - x))
  have hleft : ‖fderiv ℝ f x (y - x)‖ = ε * ‖fderiv ℝ f x v‖ := by
    rw [hstepEq, map_smul, norm_smul, Real.norm_of_nonneg hε.le]
  rw [hstepNorm] at htaylor
  have hmul : ε * ‖fderiv ℝ f x v‖ ≤ 2 * B + K * ε * ε := by
    rw [← hleft]
    exact hnorm.trans (add_le_add hvalues htaylor)
  apply le_of_mul_le_mul_left (a := ε) _ hε
  calc
    ε * ‖fderiv ℝ f x v‖ ≤ 2 * B + K * ε * ε := hmul
    _ = ε * (2 * B / ε + K * ε) := by
      rw [mul_add, mul_div_cancel₀ _ hε.ne']
      ring



theorem norm_fderiv_le_on_ball_of_hessian_bound
    {f : E → F} {center x : E} {r R B K ε : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hε : 0 < ε) (hbuffer : r + ε ≤ R)
    (hf : ∀ y ∈ Metric.ball center R, DifferentiableAt ℝ f y)
    (hdf : ∀ y ∈ Metric.ball center R, DifferentiableAt ℝ (fderiv ℝ f) y)
    (hvalue : ∀ y ∈ Metric.ball center R, ‖f y‖ ≤ B)
    (hhessian : ∀ y ∈ Metric.ball center R, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ K)
    (hx : x ∈ Metric.ball center r) :
    ‖fderiv ℝ f x‖ ≤ 2 * B / ε + K * ε := by
  have hrR : r ≤ R := by linarith
  apply norm_fderiv_le_of_hessian_bound (convex_ball center R) hB hK hε
    hf hdf hvalue hhessian (Metric.ball_subset_ball hrR hx)
  intro v hv
  rw [Metric.mem_ball] at hx ⊢
  calc
    dist (x + ε • v) center ≤ dist (x + ε • v) x + dist x center := dist_triangle _ _ _
    _ = ε + dist x center := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hε.le, hv, mul_one]
    _ < ε + r := by linarith
    _ ≤ R := by linarith

end Poincare.Parabolic.Interior
