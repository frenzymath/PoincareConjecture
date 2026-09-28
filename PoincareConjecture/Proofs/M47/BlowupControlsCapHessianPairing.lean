import PoincareConjecture.Proofs.M47.BlowupControlsCapHessianContraction
import PoincareConjecture.Proofs.M47.BlowupControlsCapTensorAction

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "Idx" => Fin 4 → I

theorem cap_sum_four_tuple (f : Idx → ℝ) :
    (∑ a : Idx, f a) = ∑ i : I, ∑ j : I, ∑ k : I, ∑ l : I, f ![i, j, k, l] := by
  let e : (I × (I × (I × I))) ≃ Idx :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      invFun := fun a => (a 0, a 1, a 2, a 3)
      left_inv := fun _ => rfl
      right_inv := by intro a; funext j; fin_cases j <;> rfl }
  have h := e.sum_comp f
  calc
    _ = ∑ p : I × (I × (I × I)), f (e p) := h.symm
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      rfl

theorem cap_hessian_scalar_pairing_le
    (A : I → I → ℝ) (hA : ∀ i j, A i j = A j i)
    (H : I → I → I → I → ℝ) (hH : ∀ i j k l, H i j l k = H i j k l) :
    |∑ i, ∑ j, ∑ k, ∑ l, (A i j * A k l / 2) *
      (H k i j l + H k j i l - H k l i j - H i k j l - H i j k l + H i l k j)| ≤
      ‖capScalarHessianComponents
        (WithLp.toLp 2 (fun p : I × I => A p.1 p.2))‖ *
        ‖(WithLp.toLp 2 (fun a : Idx => H (a 0) (a 1) (a 2) (a 3)) :
          EuclideanSpace ℝ Idx)‖ := by
  let K := fun a : Idx => H (a 0) (a 1) (a 2) (a 3)
  have hs (a : Idx) : K (fun j => a ((Equiv.swap 2 3) j)) = K a := by
    change H (a 0) (a 1) (a 3) (a 2) = H (a 0) (a 1) (a 2) (a 3)
    exact hH _ _ _ _
  have hc := cap_hessian_scalar_contraction A hA K hs
  rw [cap_sum_four_tuple] at hc
  have hb := cap_array_pairing_abs_le
    (capScalarHessianComponents (WithLp.toLp 2 (fun p : I × I => A p.1 p.2))) K
  rw [← hc] at hb
  exact hb

end PoincareConjecture.M47
