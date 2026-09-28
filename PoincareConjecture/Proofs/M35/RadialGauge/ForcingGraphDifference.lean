import PoincareConjecture.Proofs.M35.RadialGauge.SourceHessian









set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace PoincareConjecture.M35.RadialGauge

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem graph_derivative_difference_norm_le
    (P Q : (X × ℝ) →L[ℝ] F) (p q : X →L[ℝ] ℝ) :
    ‖P.comp ((ContinuousLinearMap.id ℝ X).prod p) -
      Q.comp ((ContinuousLinearMap.id ℝ X).prod q)‖ ≤
      ‖P - Q‖ * (1 + ‖p‖) + ‖Q (0, 1)‖ * ‖p - q‖ := by
  have heq : P.comp ((ContinuousLinearMap.id ℝ X).prod p) -
      Q.comp ((ContinuousLinearMap.id ℝ X).prod q) =
      (P - Q).comp ((ContinuousLinearMap.id ℝ X).prod p) +
        (p - q).smulRight (Q (0, 1)) := by
    ext v
    change P (v, p v) - Q (v, q v) =
      (P (v, p v) - Q (v, p v)) + (p v - q v) • Q (0, 1)
    have hpair : (v, p v) = (v, q v) + (p v - q v) • (0, (1 : ℝ)) := by
      ext <;> simp
    have hQ : Q (v, p v) = Q (v, q v) + (p v - q v) • Q (0, 1) := by
      rw [hpair, map_add, map_smul]
    rw [hQ]
    abel
  have hspace : ‖(P - Q).comp (ContinuousLinearMap.inl ℝ X ℝ)‖ ≤ ‖P - Q‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      Prod.norm_def, norm_zero, max_eq_left (norm_nonneg v)] using (P - Q).le_opNorm (v, 0)
  have hscalar : ‖(P - Q) (0, 1)‖ ≤ ‖P - Q‖ := by
    simpa only [Prod.norm_def, norm_zero, norm_one,
      max_eq_right zero_le_one, mul_one] using (P - Q).le_opNorm (0, 1)
  rw [heq]
  have h := norm_add_le_of_le (graph_derivative_norm_le_general (P - Q) p)
    (le_refl ‖(p - q).smulRight (Q (0, 1))‖)
  rw [ContinuousLinearMap.norm_smulRight_apply] at h
  nlinarith only [h, hspace, mul_le_mul_of_nonneg_right hscalar (norm_nonneg p)]



theorem forcing_graph_fderiv_difference_norm_le
    {A : X → ℝ → F} {u v : X → ℝ} {x : X} {eta M2 M3 : ℝ}
    (hM3 : 0 ≤ M3)
    (hAu : DifferentiableAt ℝ (fun p : X × ℝ => A p.1 p.2) (x, u x))
    (hAv : DifferentiableAt ℝ (fun p : X × ℝ => A p.1 p.2) (x, v x))
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hp : ‖fderiv ℝ u x‖ ≤ eta)
    (hscalar : ‖fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, v x) (0, 1)‖ ≤ M2)
    (hlip : ‖fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, u x) -
      fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, v x)‖ ≤ M3 * |u x - v x|) :
    ‖fderiv ℝ (fun y => A y (u y) - A y (v y)) x‖ ≤
      M3 * (1 + eta) * |u x - v x| + M2 * ‖fderiv ℝ u x - fderiv ℝ v x‖ := by
  have hgu := hAu.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hu.hasFDerivAt)
  have hgv := hAv.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hv.hasFDerivAt)
  have heq : fderiv ℝ (fun y => A y (u y) - A y (v y)) x =
      (fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, u x)).comp
        ((ContinuousLinearMap.id ℝ X).prod (fderiv ℝ u x)) -
      (fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, v x)).comp
        ((ContinuousLinearMap.id ℝ X).prod (fderiv ℝ v x)) := (hgu.sub hgv).fderiv
  rw [heq]
  have h := graph_derivative_difference_norm_le
    (fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, u x))
    (fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, v x))
    (fderiv ℝ u x) (fderiv ℝ v x)
  have h1 := mul_le_mul hlip (show 1 + ‖fderiv ℝ u x‖ ≤ 1 + eta by linarith only [hp])
    (show 0 ≤ 1 + ‖fderiv ℝ u x‖ by positivity)
    (mul_nonneg hM3 (abs_nonneg _))
  have h2 := mul_le_mul_of_nonneg_right hscalar
    (norm_nonneg (fderiv ℝ u x - fderiv ℝ v x))
  nlinarith only [h, h1, h2]

end PoincareConjecture.M35.RadialGauge
