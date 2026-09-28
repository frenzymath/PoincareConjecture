import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem saddle_smoothTransition_regular :
    (∀ t ∈ Ioo (0 : ℝ) 1, 0 < deriv Real.smoothTransition t) ∧
      StrictMonoOn Real.smoothTransition (Icc (0 : ℝ) 1) := by
  have hg (t : ℝ) : HasDerivAt expNegInvGlue
      (t⁻¹ ^ 2 * expNegInvGlue t) t := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
      (1 : Polynomial ℝ) t
  have hp (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      0 < deriv Real.smoothTransition t := by
    have hdt : HasDerivAt (fun s : ℝ => expNegInvGlue (1 - s))
        (-(1 - t)⁻¹ ^ 2 * expNegInvGlue (1 - t)) t := by
      simpa only [Function.comp_def, mul_neg, mul_one, neg_mul] using
        (hg (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)
    have hd := (hg t).div ((hg t).add hdt)
      (Real.smoothTransition.pos_denom t).ne'
    change HasDerivAt Real.smoothTransition
      ((t⁻¹ ^ 2 * expNegInvGlue t *
          (expNegInvGlue t + expNegInvGlue (1 - t)) -
        expNegInvGlue t *
          (t⁻¹ ^ 2 * expNegInvGlue t +
            -(1 - t)⁻¹ ^ 2 * expNegInvGlue (1 - t))) /
        (expNegInvGlue t + expNegInvGlue (1 - t)) ^ 2) t at hd
    rw [hd.deriv]
    apply div_pos
    · rw [show
        t⁻¹ ^ 2 * expNegInvGlue t *
            (expNegInvGlue t + expNegInvGlue (1 - t)) -
          expNegInvGlue t *
            (t⁻¹ ^ 2 * expNegInvGlue t +
              -(1 - t)⁻¹ ^ 2 * expNegInvGlue (1 - t)) =
        expNegInvGlue t * expNegInvGlue (1 - t) *
          (t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) by ring]
      exact mul_pos (mul_pos (expNegInvGlue.pos_of_pos ht.1)
        (expNegInvGlue.pos_of_pos (by linarith [ht.2])))
        (add_pos (sq_pos_of_pos (inv_pos.mpr ht.1))
          (sq_pos_of_pos (inv_pos.mpr (by linarith [ht.2]))))
    · exact sq_pos_of_pos (Real.smoothTransition.pos_denom t)
  refine ⟨hp, strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    Real.smoothTransition.continuous.continuousOn ?_⟩
  intro t ht
  rw [interior_Icc] at ht
  exact hp t ht

end PoincareConjecture.M25.Topology3D
