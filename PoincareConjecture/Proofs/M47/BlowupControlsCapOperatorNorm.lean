import PoincareConjecture.Proofs.M47.BlowupControlsCapTensorNormAlgebra
import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseDerivative
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M47

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem cap_operatorComponents_adjoint_norm (L : V →L[ℝ] V) :
    ‖capOperatorComponents (ContinuousLinearMap.adjoint L)‖ =
      ‖capOperatorComponents L‖ := by
  have heq : capOperatorComponents (ContinuousLinearMap.adjoint L) =
      WithLp.toLp 2 (fun p : Fin 3 × Fin 3 => capOperatorComponents L (p.2, p.1)) := by
    ext p
    simp only [capOperatorComponents, WithLp.ofLp_toLp,
      ContinuousLinearMap.adjoint_inner_right]
    exact real_inner_comm _ _
  rw [heq]
  exact cap_array_norm_reindex (Equiv.prodComm (Fin 3) (Fin 3)) (capOperatorComponents L)

theorem cap_operatorComponents_right_comp_norm_le (K L : V →L[ℝ] V) :
    ‖capOperatorComponents (K.comp L)‖ ≤ ‖L‖ * ‖capOperatorComponents K‖ := by
  rw [← cap_operatorComponents_adjoint_norm (K.comp L), ContinuousLinearMap.adjoint_comp]
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint L‖ *
        ‖capOperatorComponents (ContinuousLinearMap.adjoint K)‖ :=
      cap_operatorComponents_comp_norm_le _ _
    _ = _ := by rw [LinearIsometryEquiv.norm_map, cap_operatorComponents_adjoint_norm]

theorem cap_inverse_derivative_components_norm_le
    {A : V → (V →L[ℝ] V)} {x v : V}
    (hA : DifferentiableAt ℝ A x) (hi : (A x).IsInvertible) :
    ‖capOperatorComponents (fderiv ℝ (fun y => (A y).inverse) x v)‖ ≤
      ‖(A x).inverse‖ ^ 2 * ‖capOperatorComponents (fderiv ℝ A x v)‖ := by
  rw [cap_inverse_fderiv_apply A hA hi v, cap_operatorComponents_neg, norm_neg]
  calc
    _ ≤ ‖(A x).inverse‖ *
        ‖capOperatorComponents ((fderiv ℝ A x v).comp (A x).inverse)‖ :=
      cap_operatorComponents_comp_norm_le _ _
    _ ≤ ‖(A x).inverse‖ *
        (‖(A x).inverse‖ * ‖capOperatorComponents (fderiv ℝ A x v)‖) :=
      mul_le_mul_of_nonneg_left (cap_operatorComponents_right_comp_norm_le _ _)
        (norm_nonneg _)
    _ = _ := by ring

end PoincareConjecture.M47
