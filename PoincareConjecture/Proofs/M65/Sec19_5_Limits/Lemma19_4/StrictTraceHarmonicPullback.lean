import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceEquation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchHarmonicEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65StrictTrace

open M65Branch

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem harmonicMatrix_comp_holomorphic (D : LeviCivitaData g)
    {G : ℂ → EuclideanSpace ℝ (Fin n)} {psi : ℂ → ℂ} {z p : ℂ}
    (hG : DifferentiableAt ℝ G (psi z)) (hpsi : HasDerivAt psi p z) :
    harmonicMatrix D (G ∘ psi) z = star p • harmonicMatrix D G (psi z) := by
  have hd := hG.hasFDerivAt.comp z (hpsi.hasFDerivAt.restrictScalars ℝ)
  have hcol (v : ℂ) : fderiv ℝ (G ∘ psi) z v = fderiv ℝ G (psi z) (v * p) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      congrArg (fun T : ℂ →L[ℝ] EuclideanSpace ℝ (Fin n) => T v) hd.fderiv
  let L : ℂ →L[ℝ] ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
    complexifyOperator.comp
      ((M65Gauss.connectionCoefficient D (G (psi z))).comp (fderiv ℝ G (psi z)))
  have hlin : L p + I • L (I * p) = star p • (L 1 + I • L I) := by
    have hstar : star p = (p.re : ℂ) - (p.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hstar, realLinear_apply_complex L p, realLinear_apply_complex L (I * p)]
    simp only [I_mul_re, I_mul_im, ofReal_neg, smul_add, smul_smul,
      sub_mul, mul_assoc, I_mul_I, mul_neg_one, sub_neg_eq_add]
    module
  simp only [harmonicMatrix, hcol, one_mul, Function.comp_apply]
  change (-(2 : ℂ)⁻¹) • (L p + I • L (I * p)) =
    star p • ((-(2 : ℂ)⁻¹) • (L 1 + I • L I))
  rw [hlin, smul_comm]

theorem harmonic_matrix_equation_comp_holomorphic (D : LeviCivitaData g)
    {G : ℂ → EuclideanSpace ℝ (Fin n)} {U W : Set ℂ} {psi : ℂ → ℂ}
    (hU : IsOpen U) (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G U)
    (hpsi : ContDiffOn ℂ ∞ psi W) (hmap : MapsTo psi W U)
    (heq : ∀ w ∈ U, dbar (complexGradient G) w =
      harmonicMatrix D G w (complexGradient G w)) {z : ℂ} (hz : z ∈ W) :
    dbar (complexGradient (G ∘ psi)) z =
      harmonicMatrix D (G ∘ psi) z (complexGradient (G ∘ psi) z) := by
  have hgrad : ContDiffOn ℝ 1 (complexGradient G) U := contDiffOn_complexGradient hU hG
  have hGd (w : ℂ) (hw : w ∈ W) : DifferentiableAt ℝ G (psi w) :=
    (hG.contDiffAt (hU.mem_nhds (hmap hw))).differentiableAt (by simp)
  have hpd (w : ℂ) (hw : w ∈ W) : HasDerivAt psi (deriv psi w) w :=
    ((hpsi.contDiffAt (hW.mem_nhds hw)).differentiableAt (by simp)).hasDerivAt
  have hderiv : ContDiffOn ℂ ∞ (deriv psi) W := hpsi.deriv_of_isOpen hW (by simp)
  have hp : DifferentiableAt ℂ (deriv psi) z :=
    (hderiv.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
  have hfield : complexGradient (G ∘ psi) =ᶠ[𝓝 z]
      fun w => deriv psi w • complexGradient G (psi w) := by
    filter_upwards [hW.mem_nhds hz] with w hw
    exact complexGradient_comp_holomorphic (hGd w hw) (hpd w hw)
  have hbar : dbar (complexGradient (G ∘ psi)) z =
      dbar (fun w => deriv psi w • complexGradient G (psi w)) z :=
    congrArg dbarLinear hfield.fderiv_eq
  rw [hbar, matrix_equation_holomorphic_pullback
    ((hgrad.contDiffAt (hU.mem_nhds (hmap hz))).differentiableAt one_ne_zero)
    (hpd z hz) hp (heq _ (hmap hz)),
    harmonicMatrix_comp_holomorphic D (hGd z hz) (hpd z hz),
    complexGradient_comp_holomorphic (hGd z hz) (hpd z hz)]

end PoincareConjecture.M65StrictTrace
