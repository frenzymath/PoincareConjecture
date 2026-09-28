import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false

open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fderiv_stereoInvFunAux_apply (v w a : E) :
    fderiv ℝ (stereoInvFunAux v) w a =
      (4 / (‖w‖ ^ 2 + 4)) • a -
        (8 * inner ℝ w a / (‖w‖ ^ 2 + 4) ^ 2) • w +
        (16 * inner ℝ w a / (‖w‖ ^ 2 + 4) ^ 2) • v := by
  have hne : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have hn := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt w (hn.add_const 4)
  have h := hi.smul (((hasFDerivAt_id w).const_smul (4 : ℝ)).add
    ((hn.sub_const 4).smul_const v))
  change HasFDerivAt (stereoInvFunAux v) _ w at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul,
    Function.comp_apply, Pi.add_apply, Pi.smul_apply, id_eq]
  match_scalars <;> field_simp <;> ring

theorem inner_fderiv_stereoInvFunAux (v w a b : E) (hv : ‖v‖ = 1)
    (hw : inner ℝ v w = 0) (ha : inner ℝ v a = 0) (hb : inner ℝ v b = 0) :
    inner ℝ (fderiv ℝ (stereoInvFunAux v) w a)
      (fderiv ℝ (stereoInvFunAux v) w b) =
        16 / (‖w‖ ^ 2 + 4) ^ 2 * inner ℝ a b := by
  have hne : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have hwv : inner ℝ w v = 0 := (real_inner_comm v w).trans hw
  have hav : inner ℝ a v = 0 := (real_inner_comm v a).trans ha
  rw [fderiv_stereoInvFunAux_apply, fderiv_stereoInvFunAux_apply]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, conj_trivial, hw, hb, hwv, hav,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_zero, sub_zero, zero_add,
    add_zero, real_inner_comm a w]
  field_simp
  ring

theorem inner_fderiv_stereoInvFunAux_comp_linearIsometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : F →ₗᵢ[ℝ] E) (v : E) (hv : ‖v‖ = 1)
    (hL : ∀ a : F, inner ℝ v (L a) = 0) (x a b : F) :
    inner ℝ (fderiv ℝ (fun y => stereoInvFunAux v (L y)) x a)
      (fderiv ℝ (fun y => stereoInvFunAux v (L y)) x b) =
        16 / (‖x‖ ^ 2 + 4) ^ 2 * inner ℝ a b := by
  have h := (((contDiff_stereoInvFunAux (m := ∞) (v := v)).differentiable
    (by simp) (L x)).hasFDerivAt).comp x L.toContinuousLinearMap.hasFDerivAt
  change HasFDerivAt (fun y => stereoInvFunAux v (L y)) _ x at h
  rw [h.fderiv]
  change inner ℝ (fderiv ℝ (stereoInvFunAux v) (L x) (L a))
    (fderiv ℝ (stereoInvFunAux v) (L x) (L b)) = _
  simpa only [L.norm_map, L.inner_map_map] using
    inner_fderiv_stereoInvFunAux v (L x) (L a) (L b) hv (hL x) (hL a) (hL b)
