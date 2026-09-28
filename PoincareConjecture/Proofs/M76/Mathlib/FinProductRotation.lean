import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem finRotate_finProdFinEquiv_castSucc {n m : ℕ} (i : Fin n) (j : Fin m) :
    finRotate (n * (m + 1)) (finProdFinEquiv (i, j.castSucc)) =
      finProdFinEquiv (i, j.succ) := by
  let := i.neZero
  apply Fin.ext
  simp only [finRotate_apply, Fin.val_add, Fin.val_one', finProdFinEquiv_apply_val,
    Fin.val_castSucc, Fin.val_succ]
  rw [Nat.add_mod_mod]
  have hb := (finProdFinEquiv (i, j.succ)).isLt
  change j.val + 1 + (m + 1) * i.val < n * (m + 1) at hb
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem finRotate_finProdFinEquiv_last {n m : ℕ} (i : Fin n) :
    finRotate (n * (m + 1)) (finProdFinEquiv (i, Fin.last m)) =
      finProdFinEquiv (finRotate n i, (0 : Fin (m + 1))) := by
  let := i.neZero
  apply Fin.ext
  simp only [finRotate_apply, Fin.val_add, Fin.val_one', finProdFinEquiv_apply_val,
    Fin.val_last, Fin.val_zero, zero_add, Nat.add_mod_mod]
  calc
    (m + (m + 1) * i.val + 1) % (n * (m + 1)) =
        ((m + 1) * (i.val + 1)) % ((m + 1) * n) := by
      congr 1 <;> ring
    _ = (m + 1) * ((i.val + 1) % n) := Nat.mul_mod_mul_left _ _ _
