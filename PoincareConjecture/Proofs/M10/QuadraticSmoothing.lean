import PoincareConjecture.Proofs.M10.MollifierConcavity

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def euclideanQuadratic (K : ℝ) (x : E) : ℝ := K * ‖x‖ ^ 2 / 2

theorem euclideanQuadratic_contDiff (K : ℝ) : ContDiff ℝ ∞ (euclideanQuadratic (E := E) K) :=
  (contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2

theorem euclideanQuadratic_fderiv (K : ℝ) (x : E) :
    fderiv ℝ (euclideanQuadratic K) x = K • innerSL ℝ x := by
  have heq : euclideanQuadratic (E := E) K = fun y ↦ (K / 2) • ‖y‖ ^ 2 := by
    funext y
    simp only [euclideanQuadratic, smul_eq_mul]
    ring
  rw [heq]
  change fderiv ℝ ((K / 2) • fun y : E ↦ ‖y‖ ^ 2) x = _
  rw [((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (K / 2)).fderiv]
  ext v
  simp only [smul_apply, two_smul, add_apply,
    smul_eq_mul]
  ring

theorem second_fderiv_add_at {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have heq : fderiv ℝ (fun y ↦ f y + g y) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hy'
    exact fderiv_fun_add (hy.differentiableAt two_ne_zero) (hy'.differentiableAt two_ne_zero)
  rw [heq.fderiv_eq]
  exact fderiv_fun_add ((hf.fderiv_right (by norm_num)).differentiableAt one_ne_zero)
    ((hg.fderiv_right (by norm_num)).differentiableAt one_ne_zero)

theorem norm_fderiv_add_quadratic_le {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hfd : Differentiable ℝ f) {K : ℝ} (hK : 0 ≤ K) {x x₀ : E} {r : ℝ}
    (hx : x ∈ ball x₀ r) :
    ‖fderiv ℝ (fun y ↦ f y + euclideanQuadratic K y) x‖ ≤
      L + K * (‖x₀‖ + r) := by
  have hq := (euclideanQuadratic_contDiff (E := E) K).differentiable (by simp)
  rw [fderiv_fun_add (hfd x) (hq x), euclideanQuadratic_fderiv]
  have hnorm : ‖x‖ ≤ ‖x₀‖ + r := by
    calc
      ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ r + ‖x₀‖ := add_le_add (mem_ball_iff_norm.mp hx).le le_rfl
      _ = ‖x₀‖ + r := add_comm _ _
  calc
    _ ≤ ‖fderiv ℝ f x‖ + ‖K • innerSL ℝ x‖ := norm_add_le _ _
    _ = ‖fderiv ℝ f x‖ + K * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hK, innerSL_apply_norm]
    _ ≤ L + K * (‖x₀‖ + r) := add_le_add (norm_fderiv_le_of_lipschitz ℝ hf)
      (mul_le_mul_of_nonneg_left hnorm hK)

theorem second_fderiv_add_quadratic_le {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiff ℝ 2 f) (hconc : ConcaveOn ℝ U f)
    {x : E} (hx : x ∈ U) (K : ℝ) (v : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f y + euclideanQuadratic K y)) x v v ≤ K * ‖v‖ ^ 2 := by
  have hq := (euclideanQuadratic_contDiff (E := E) K).of_le
    (by decide : (2 : ℕ∞ω) ≤ ∞)
  have hs := second_deriv_sub_norm_sq_on_line (f := fun y ↦ f y + euclideanQuadratic K y)
    x v (t := 0) (by simpa only [zero_smul, add_zero] using (hf.add hq).contDiffAt) K
  simp only [euclideanQuadratic, add_sub_cancel_right, zero_smul, add_zero] at hs
  rw [second_deriv_affine_line hf.contDiffAt v] at hs
  have hn := second_fderiv_nonpos_of_concaveOn hU hf.contDiffOn hconc hx v
  simp only [euclideanQuadratic]
  linarith

end PoincareConjecture.M10
