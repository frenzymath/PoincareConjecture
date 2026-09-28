import PoincareConjecture.Proofs.M35.Uniqueness.Heat.EquivalentIntegralHeat
import Mathlib.Analysis.InnerProductSpace.LaxMilgram









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def shiftedEllipticOperator (I : V →L[ℝ] H) (P : V →L[ℝ] V)
    (L : V →L[ℝ] H) (c C : ℝ) : V →L[ℝ] V :=
  P - I.adjoint.comp L + (1 + C ^ 2 / c) • I.adjoint.comp I

theorem shiftedEllipticOperator_coercive (I : V →L[ℝ] H) (P : V →L[ℝ] V)
    (L : V →L[ℝ] H) {c C : ℝ} (hc : 0 < c) (hL : ‖L‖ ≤ C)
    (hP : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ u (P u) + ‖I u‖ ^ 2) (u : V) :
    c / 2 * ‖u‖ ^ 2 ≤ inner ℝ u (shiftedEllipticOperator I P L c C u) := by
  have hl : inner ℝ (I u) (L u) ≤ ‖I u‖ * (C * ‖u‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((L.le_opNorm u).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))) (norm_nonneg _))
  have hp := mul_le_mul_of_nonneg_left (hP u) hc.le
  have hll := mul_le_mul_of_nonneg_left hl hc.le
  have hdiv : c * (C ^ 2 / c) * ‖I u‖ ^ 2 = C ^ 2 * ‖I u‖ ^ 2 := by
    rw [mul_div_cancel₀ _ hc.ne']
  simp only [shiftedEllipticOperator, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    smul_apply, inner_add_right, inner_sub_right, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  apply (mul_le_mul_iff_left₀ hc).mp
  nlinarith only [hp, hll, hdiv, sq_nonneg (c * ‖u‖ - C * ‖I u‖),
    sq_nonneg (C * ‖I u‖)]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem isInvertible_of_inner_coercive (A : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ u (A u)) : A.IsInvertible := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := (innerSL ℝ).comp A
  have hB : IsCoercive B := by
    refine ⟨c, hc, ?_⟩
    intro u
    change c * ‖u‖ * ‖u‖ ≤ inner ℝ (A u) u
    simpa only [real_inner_comm, pow_two, mul_assoc] using hA u
  refine ⟨hB.continuousLinearEquivOfBilin, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro w
  exact hB.continuousLinearEquivOfBilin_apply u w

theorem shiftedEllipticOperator_isInvertible (I : V →L[ℝ] H) (P : V →L[ℝ] V)
    (L : V →L[ℝ] H) {c C : ℝ} (hc : 0 < c) (hL : ‖L‖ ≤ C)
    (hP : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ u (P u) + ‖I u‖ ^ 2) :
    (shiftedEllipticOperator I P L c C).IsInvertible :=
  isInvertible_of_inner_coercive _ (half_pos hc)
    (shiftedEllipticOperator_coercive I P L hc hL hP)

end PoincareConjecture.M35.Uniqueness.Heat
