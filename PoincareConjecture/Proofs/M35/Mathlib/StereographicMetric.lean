import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic









set_option autoImplicit false

namespace PoincareConjecture.M35

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]



theorem fderiv_stereoInvFunAux_apply (v w a : V) :
    fderiv ℝ (stereoInvFunAux v) w a =
      (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • a + (2 * inner ℝ w a) • v) +
      (-((‖w‖ ^ 2 + 4) ^ 2)⁻¹ * (2 * inner ℝ w a)) •
        ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v) := by
  have hd : ‖w‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have hn := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hi := (hasDerivAt_inv hd).comp_hasFDerivAt w (hn.add_const 4)
  have hv := ((hasFDerivAt_id w).const_smul (4 : ℝ)).add
    ((hn.sub_const 4).smul_const v)
  have h := hi.smul hv
  change HasFDerivAt (stereoInvFunAux v) _ w at h
  simpa using congrArg (fun L : V →L[ℝ] V => L a) h.fderiv



theorem inner_fderiv_stereoInvFunAux (v w a b : V)
    (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0)
    (ha : inner ℝ v a = 0) (hb : inner ℝ v b = 0) :
    inner ℝ (fderiv ℝ (stereoInvFunAux v) w a)
      (fderiv ℝ (stereoInvFunAux v) w b) =
      16 / (‖w‖ ^ 2 + 4) ^ 2 * inner ℝ a b := by
  have hd : ‖w‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have hvw : inner ℝ w v = 0 := by rwa [real_inner_comm]
  have hav : inner ℝ a v = 0 := by rwa [real_inner_comm]
  rw [fderiv_stereoInvFunAux_apply, fderiv_stereoInvFunAux_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hw, hb, hvw, hav, real_inner_self_eq_norm_sq, hv]
  rw [real_inner_comm a w]
  field_simp
  ring



theorem hasFDerivAt_stereographicMetricFactor (K : ℝ) (w : V) :
    HasFDerivAt (fun x : V => K / (‖x‖ ^ 2 + 4) ^ 2)
      ((-4 * K / (‖w‖ ^ 2 + 4) ^ 3) • innerSL ℝ w) w := by
  have hd : (‖w‖ ^ 2 + 4) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hn := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h := ((hasDerivAt_inv hd).comp_hasFDerivAt w
    ((hn.add_const 4).pow 2)).const_mul K
  convert! h using 1
  ext a
  simp
  field_simp
  ring

end PoincareConjecture.M35
