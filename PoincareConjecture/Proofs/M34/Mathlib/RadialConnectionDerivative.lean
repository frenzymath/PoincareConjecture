import PoincareConjecture.Proofs.M34.Mathlib.RadialConnection
import Mathlib.Tactic.Module











set_option autoImplicit false

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem fderiv_radialChristoffel {A B C : ℝ → ℝ} {A' B' C' : ℝ} {x : E}
    (hx : x ≠ 0) (hA : HasDerivAt A A' ‖x‖) (hB : HasDerivAt B B' ‖x‖)
    (hC : HasDerivAt C C' ‖x‖) (u v w : E) :
    fderiv ℝ (fun y => radialChristoffel (A ‖y‖) (B ‖y‖) (C ‖y‖) y u v) x w =
      (A' / ‖x‖ * inner ℝ x w) • (inner ℝ x u • v + inner ℝ x v • u) +
      A ‖x‖ • (inner ℝ w u • v + inner ℝ w v • u) +
      (B' / ‖x‖ * inner ℝ x w * inner ℝ u v) • x +
      (B ‖x‖ * inner ℝ u v) • w +
      (C' / ‖x‖ * inner ℝ x w * inner ℝ x u * inner ℝ x v +
        C ‖x‖ * (inner ℝ w u * inner ℝ x v + inner ℝ x u * inner ℝ w v)) • x +
      (C ‖x‖ * inner ℝ x u * inner ℝ x v) • w := by
  have hu := (hasFDerivAt_id x).inner ℝ (hasFDerivAt_const u x)
  have hv := (hasFDerivAt_id x).inner ℝ (hasFDerivAt_const v x)
  have h := (((hasFDerivAt_radial hx hA).smul
    ((hu.smul_const v).add (hv.smul_const u))).add
    (((hasFDerivAt_radial hx hB).mul_const (inner ℝ u v)).smul (hasFDerivAt_id x))).add
    ((((hasFDerivAt_radial hx hC).mul hu).mul hv).smul (hasFDerivAt_id x))
  change HasFDerivAt
    (fun y => radialChristoffel (A ‖y‖) (B ‖y‖) (C ‖y‖) y u v) _ x at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
    ContinuousLinearMap.smulRight_apply, fderivInnerCLM_apply, inner_zero_right,
    zero_add, innerSL_apply_apply, smul_eq_mul, Pi.mul_apply, Pi.add_apply,
    id_eq]
  module




theorem radialChristoffel_curvature_expression {A B C : ℝ → ℝ} {A' B' C' : ℝ}
    {x : E} (hx : x ≠ 0) (hA : HasDerivAt A A' ‖x‖) (hB : HasDerivAt B B' ‖x‖)
    (hC : HasDerivAt C C' ‖x‖) (u v w : E) :
    let a := A ‖x‖
    let b := B ‖x‖
    let c := C ‖x‖
    fderiv ℝ (fun y => radialChristoffel (A ‖y‖) (B ‖y‖) (C ‖y‖) y v w) x u +
        radialChristoffel a b c x u (radialChristoffel a b c x v w) -
      (fderiv ℝ (fun y => radialChristoffel (A ‖y‖) (B ‖y‖) (C ‖y‖) y u w) x v +
        radialChristoffel a b c x v (radialChristoffel a b c x u w)) =
      (b - a + a * b * ‖x‖ ^ 2) • (inner ℝ v w • u - inner ℝ u w • v) +
      ((c - A' / ‖x‖ + a ^ 2 + a * c * ‖x‖ ^ 2) * inner ℝ x w) •
        (inner ℝ x v • u - inner ℝ x u • v) +
      ((B' / ‖x‖ - c + b ^ 2 + b * c * ‖x‖ ^ 2) *
        (inner ℝ x u * inner ℝ v w - inner ℝ x v * inner ℝ u w)) • x := by
  dsimp only
  rw [fderiv_radialChristoffel hx hA hB hC, fderiv_radialChristoffel hx hA hB hC]
  simp only [radialChristoffel, inner_add_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm u v, real_inner_comm x u, real_inner_comm x v]
  module

end Poincare
