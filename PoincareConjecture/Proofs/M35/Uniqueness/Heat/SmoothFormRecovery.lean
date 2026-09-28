import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ShiftedEllipticInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def ellipticFormRecovery (I : V →L[ℝ] H) (P : ℝ → V →L[ℝ] V)
    (L : ℝ → V →L[ℝ] H) (c C : ℝ) (U : ℝ → H) (t : ℝ) : V :=
  (shiftedEllipticOperator I (P t) (L t) c C).inverse
    (I.adjoint ((1 + C ^ 2 / c) • U t - deriv U t))

theorem contDiffAt_ellipticFormRecovery (I : V →L[ℝ] H) (P : ℝ → V →L[ℝ] V)
    (L : ℝ → V →L[ℝ] H) {c C t : ℝ} (hc : 0 < c) (hL : ‖L t‖ ≤ C)
    (hP : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ u (P t u) + ‖I u‖ ^ 2)
    (hPc : ContDiffAt ℝ ∞ P t) (hLc : ContDiffAt ℝ ∞ L t)
    {U : ℝ → H} (hU : ContDiffAt ℝ ∞ U t) :
    ContDiffAt ℝ ∞ (ellipticFormRecovery I P L c C U) t := by
  have hG : ContDiffAt ℝ ∞ (fun s => shiftedEllipticOperator I (P s) (L s) c C) t :=
    (hPc.sub (contDiffAt_const.clm_comp hLc)).add contDiffAt_const
  have hGi := shiftedEllipticOperator_isInvertible I (P t) (L t) hc hL hP
  have hi := hGi.contDiffAt_map_inverse.comp t hG
  have hdU : ContDiffAt ℝ ∞ (deriv U) t := hU.derivWithin (by simp)
  exact hi.clm_apply
    (I.adjoint.contDiff.comp_contDiffAt t ((contDiffAt_const.smul hU).sub hdU))

theorem ellipticFormRecovery_eq (I : V →L[ℝ] H) (P : ℝ → V →L[ℝ] V)
    (L : ℝ → V →L[ℝ] H) {c C t : ℝ} (hc : 0 < c) (hL : ‖L t‖ ≤ C)
    (hP : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ u (P t u) + ‖I u‖ ^ 2)
    {U : ℝ → H} {v : V} (hgraph : I v = U t)
    (heq : I.adjoint (deriv U t) = I.adjoint (L t v) - P t v) :
    ellipticFormRecovery I P L c C U t = v := by
  apply (shiftedEllipticOperator_isInvertible I (P t) (L t) hc hL hP).inverse_apply_eq.mpr
  simp only [map_sub, map_smul, heq, shiftedEllipticOperator, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, smul_apply, hgraph]
  abel

theorem ellipticFormRecovery_equation (I : V →L[ℝ] H) (P : ℝ → V →L[ℝ] V)
    (L : ℝ → V →L[ℝ] H) {c C t : ℝ} (hc : 0 < c) (hL : ‖L t‖ ≤ C)
    (hP : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ u (P t u) + ‖I u‖ ^ 2)
    {U : ℝ → H} (hgraph : I (ellipticFormRecovery I P L c C U t) = U t) :
    I.adjoint (deriv U t) = I.adjoint (L t (ellipticFormRecovery I P L c C U t)) -
      P t (ellipticFormRecovery I P L c C U t) := by
  have he := (shiftedEllipticOperator_isInvertible I (P t) (L t) hc hL hP).self_apply_inverse
    (I.adjoint ((1 + C ^ 2 / c) • U t - deriv U t))
  change shiftedEllipticOperator I (P t) (L t) c C
    (ellipticFormRecovery I P L c C U t) = _ at he
  simp only [shiftedEllipticOperator, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    smul_apply, hgraph, map_sub, map_smul] at he
  have hcancel : P t (ellipticFormRecovery I P L c C U t) -
      I.adjoint (L t (ellipticFormRecovery I P L c C U t)) = -I.adjoint (deriv U t) := by
    apply add_right_cancel (b := (1 + C ^ 2 / c) • I.adjoint (U t))
    exact he.trans (by abel)
  simpa only [neg_neg, neg_sub] using (congrArg Neg.neg hcancel).symm

end PoincareConjecture.M35.Uniqueness.Heat
