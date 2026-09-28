import Mathlib.Logic.Equiv.Fin.Rotate
import Lean.Elab.Tactic.Omega










set_option autoImplicit false




theorem Fin.exists_cyclic_marked_split {N : ℕ} (a b : Fin (N + 3)) (hab : a ≠ b) :
    ∃ (m n : ℕ) (e : Fin ((m + 1) + (n + 1)) ≃ Fin (N + 3)),
      (∀ i, e (finRotate _ i) = finRotate _ (e i)) ∧
      e ((0 : Fin (m + 1)).castAdd (n + 1)) = a ∧
      e (Fin.natAdd (m + 1) (0 : Fin (n + 1))) = b := by
  let k := b - a
  have hk0 : k ≠ 0 := sub_ne_zero.mpr hab.symm
  have hklo : 1 ≤ k.val := by
    have h0 : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
    omega
  let m := k.val - 1
  let n := N + 3 - k.val - 1
  have hm : m + 1 = k.val := by dsimp [m]; omega
  have hsize : (m + 1) + (n + 1) = N + 3 := by
    have := k.isLt
    dsimp [m, n]
    omega
  let e := (finCongr hsize).trans (finCycle a)
  refine ⟨m, n, e, ?_, ?_, ?_⟩
  · intro i
    change finCycle a (finCongr hsize (finRotate _ i)) =
      finRotate _ (finCycle a (finCongr hsize i))
    have hrot {r s : ℕ} (h : r = s) (j : Fin r) :
        finCongr h (finRotate r j) = finRotate s (finCongr h j) := by
      subst s
      rfl
    rw [hrot]
    simp only [finCycle_apply, finRotate_apply]
    ac_rfl
  · change finCongr hsize ((0 : Fin (m + 1)).castAdd (n + 1)) + a = a
    have hz : finCongr hsize ((0 : Fin (m + 1)).castAdd (n + 1)) = 0 := by
      apply Fin.ext
      rfl
    rw [hz, zero_add]
  · change finCongr hsize (Fin.natAdd (m + 1) (0 : Fin (n + 1))) + a = b
    have heq : finCongr hsize (Fin.natAdd (m + 1) (0 : Fin (n + 1))) = k := by
      apply Fin.ext
      change m + 1 + 0 = k.val
      omega
    rw [heq]
    exact sub_add_cancel b a
