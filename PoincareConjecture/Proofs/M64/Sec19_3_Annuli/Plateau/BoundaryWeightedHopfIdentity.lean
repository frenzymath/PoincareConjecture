import PoincareConjecture.Proofs.M60.Mathlib.SUHopfCauchyRiemann

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology

namespace PoincareConjecture

open Poincare.Riemannian.RadialTransport

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem m64WeightedHarmonicPairing_cauchyRiemann
    {Gamma : P → P →L[ℝ] E →L[ℝ] E} {G : P → E →L[ℝ] E →L[ℝ] ℝ}
    {Y Z : P → E} {p : P} (d e : P) {r : ℝ} (hr : r ≠ 0)
    (hG : DifferentiableAt ℝ G p) (hY : DifferentiableAt ℝ Y p)
    (hZ : DifferentiableAt ℝ Z p)
    (hcompat : ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun q => G q b c) p v =
        G p (Gamma p v b) c + G p b (Gamma p v c))
    (hsymm : ∀ b c : E, G p b c = G p c b)
    (htor : covariantDerivative Gamma Z p d = covariantDerivative Gamma Y p e)
    (hharm : r • covariantDerivative Gamma Y p d +
      r⁻¹ • covariantDerivative Gamma Z p e = 0) :
    fderiv ℝ (fun q => r * G q (Y q) (Y q) - r⁻¹ * G q (Z q) (Z q)) p d =
        -r⁻¹ * fderiv ℝ (fun q => 2 * G q (Y q) (Z q)) p e ∧
      fderiv ℝ (fun q => r * G q (Y q) (Y q) - r⁻¹ * G q (Z q) (Z q)) p e =
        r * fderiv ℝ (fun q => 2 * G q (Y q) (Z q)) p d := by
  have hYY := (hG.clm_apply hY).clm_apply hY
  have hZZ := (hG.clm_apply hZ).clm_apply hZ
  have hYZ := (hG.clm_apply hY).clm_apply hZ
  have hscaled := congrArg (fun v : E => r • v) hharm
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hr, one_smul, smul_zero] at hscaled
  have hneg : covariantDerivative Gamma Z p e =
      -((r * r) • covariantDerivative Gamma Y p d) :=
    eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hscaled)
  have hpair (U V : P → E) (hU : DifferentiableAt ℝ U p)
      (hV : DifferentiableAt ℝ V p) (v : P) :=
    fderiv_metric_pairing hG hU hV hcompat v
  rw [fderiv_fun_sub (hYY.const_mul r) (hZZ.const_mul r⁻¹),
    fderiv_const_mul hYY, fderiv_const_mul hZZ, fderiv_const_mul hYZ]
  simp only [sub_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hpair Y Y hY hY d, hpair Z Z hZ hZ d, hpair Y Z hY hZ e,
    hpair Y Y hY hY e, hpair Z Z hZ hZ e, hpair Y Z hY hZ d, htor, hneg]
  simp only [map_neg, neg_apply, map_smul, smul_apply, smul_eq_mul]
  rw [hsymm (Y p), hsymm (Z p), hsymm (Y p), hsymm (Z p)]
  constructor <;> field_simp [hr] <;> ring

end PoincareConjecture
