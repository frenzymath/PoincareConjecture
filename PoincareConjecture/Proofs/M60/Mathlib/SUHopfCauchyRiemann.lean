import PoincareConjecture.Proofs.M60.Mathlib.CovariantPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M60

open Poincare.Riemannian.RadialTransport

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem harmonic_pairing_cauchyRiemann
    {Γ : P → P →L[ℝ] E →L[ℝ] E} {G : P → E →L[ℝ] E →L[ℝ] ℝ}
    {Y Z : P → E} {p : P} (d e : P)
    (hG : DifferentiableAt ℝ G p) (hY : DifferentiableAt ℝ Y p)
    (hZ : DifferentiableAt ℝ Z p)
    (hcompat : ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun q => G q b c) p v =
        G p (Γ p v b) c + G p b (Γ p v c))
    (hsymm : ∀ b c : E, G p b c = G p c b)
    (htor : covariantDerivative Γ Z p d = covariantDerivative Γ Y p e)
    (hharm : covariantDerivative Γ Y p d + covariantDerivative Γ Z p e = 0) :
    fderiv ℝ (fun q => G q (Y q) (Y q) - G q (Z q) (Z q)) p d =
        fderiv ℝ (fun q => -2 * G q (Y q) (Z q)) p e ∧
      fderiv ℝ (fun q => G q (Y q) (Y q) - G q (Z q) (Z q)) p e =
        -fderiv ℝ (fun q => -2 * G q (Y q) (Z q)) p d := by
  have hYY := (hG.clm_apply hY).clm_apply hY
  have hZZ := (hG.clm_apply hZ).clm_apply hZ
  have hYZ := (hG.clm_apply hY).clm_apply hZ
  have hneg : covariantDerivative Γ Z p e = -covariantDerivative Γ Y p d :=
    eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hharm)
  have hpair (U V : P → E) (hU : DifferentiableAt ℝ U p)
      (hV : DifferentiableAt ℝ V p) (v : P) :=
    fderiv_metric_pairing hG hU hV hcompat v
  rw [fderiv_fun_sub hYY hZZ, fderiv_const_mul hYZ]
  simp only [sub_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hpair Y Y hY hY d, hpair Z Z hZ hZ d,
    hpair Y Z hY hZ e, hpair Y Y hY hY e,
    hpair Z Z hZ hZ e, hpair Y Z hY hZ d, htor, hneg]
  simp only [map_neg, neg_apply]
  rw [hsymm (Y p), hsymm (Z p), hsymm (Y p), hsymm (Z p)]
  constructor <;> ring

end PoincareConjecture.M60
