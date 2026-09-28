import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Positivity










set_option autoImplicit false

open Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem norm_fderiv_zero_le_of_two_derivative_bounds
    {f : E → F} {h δ K : ℝ} (hh : 0 < h) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hf : ∀ x ∈ closedBall (0 : E) h, DifferentiableAt ℝ f x)
    (hdf : ∀ x ∈ closedBall (0 : E) h, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hvalue : ∀ x ∈ closedBall (0 : E) h, ‖f x‖ ≤ δ)
    (hsecond : ∀ x ∈ closedBall (0 : E) h, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K) :
    ‖fderiv ℝ f 0‖ ≤ 2 * δ / h + K * h := by
  let D := fderiv ℝ f 0
  let R : E → F := fun x => f x - f 0 - D x
  have h0 : (0 : E) ∈ closedBall (0 : E) h := mem_closedBall_self hh.le
  have hvariation (x : E) (hx : x ∈ closedBall (0 : E) h) :
      ‖fderiv ℝ f x - D‖ ≤ K * h := by
    have hbound := Convex.norm_image_sub_le_of_norm_fderiv_le hdf hsecond
      (convex_closedBall (0 : E) h) h0 hx
    calc
      ‖fderiv ℝ f x - D‖ ≤ K * ‖x‖ := by simpa only [D, sub_zero] using hbound
      _ ≤ K * h := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hK
  have hRderiv (x : E) (hx : x ∈ closedBall (0 : E) h) :
      HasFDerivAt R (fderiv ℝ f x - D) x :=
    ((hf x hx).hasFDerivAt.sub_const (f 0)).sub D.hasFDerivAt
  have hRbound (x : E) (hx : x ∈ closedBall (0 : E) h) :
      ‖R x‖ ≤ (K * h) * ‖x‖ := by
    have hbound := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hRderiv y hy).differentiableAt)
      (fun y hy => (hRderiv y hy).fderiv.symm ▸ hvariation y hy)
      (convex_closedBall (0 : E) h) h0 hx
    simpa only [R, map_zero, sub_self, sub_zero] using hbound
  change ‖D‖ ≤ 2 * δ / h + K * h
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hnorm : ‖h • v‖ = h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh, hv, mul_one]
  have hx : h • v ∈ closedBall (0 : E) h :=
    mem_closedBall_zero_iff.mpr hnorm.le
  have hD : ‖D (h • v)‖ ≤ 2 * δ + K * h * h := by
    calc
      ‖D (h • v)‖ = ‖(f (h • v) - f 0) - R (h • v)‖ :=
        congrArg norm (sub_sub_cancel (f (h • v) - f 0) (D (h • v))).symm
      _ ≤ ‖f (h • v) - f 0‖ + ‖R (h • v)‖ := norm_sub_le _ _
      _ ≤ (‖f (h • v)‖ + ‖f 0‖) + ‖R (h • v)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (δ + δ) + (K * h) * ‖h • v‖ :=
        add_le_add (add_le_add (hvalue _ hx) (hvalue _ h0)) (hRbound _ hx)
      _ = 2 * δ + K * h * h := by rw [hnorm, two_mul]
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hh] at hD
  calc
    ‖D v‖ ≤ (2 * δ + K * h * h) / h :=
      (le_div_iff₀ hh).mpr ((mul_comm ‖D v‖ h).le.trans hD)
    _ = 2 * δ / h + K * h := by rw [add_div, mul_div_cancel_right₀ _ hh.ne']
