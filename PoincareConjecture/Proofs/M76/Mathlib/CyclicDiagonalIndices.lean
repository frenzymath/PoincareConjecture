import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Abel










set_option autoImplicit false

private theorem finCongr_rotate {m n : ℕ} (h : m = n) (i : Fin m) :
    finCongr h (finRotate m i) = finRotate n (finCongr h i) := by
  subst n
  rfl





theorem Fin.exists_cyclic_diagonal_split {N : ℕ} (a b : Fin (N + 4))
    (hab : a ≠ b) (hba : b ≠ finRotate (N + 4) a)
    (hab' : a ≠ finRotate (N + 4) b) :
    ∃ (m n : ℕ) (e : Fin ((m + 2) + (n + 2)) ≃ Fin (N + 4)),
      m + 3 < N + 4 ∧ n + 3 < N + 4 ∧
      (∀ i, e (finRotate _ i) = finRotate _ (e i)) ∧
      e ((0 : Fin (m + 2)).castAdd (n + 2)) = a ∧
      e (Fin.natAdd (m + 2) (0 : Fin (n + 2))) = b := by
  let k := b - a
  have hk0 : k ≠ 0 := sub_ne_zero.mpr hab.symm
  have hk1 : k ≠ 1 := by
    intro h
    apply hba
    rw [finRotate_apply]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp h)
  have hkLast : k + 1 ≠ 0 := by
    intro h
    apply hab'
    rw [finRotate_apply]
    have heq : b + 1 = (k + 1) + a := by dsimp [k]; abel
    rw [h, zero_add] at heq
    exact heq.symm
  have hklo : 2 ≤ k.val := by
    have h0 : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
    have h1 : k.val ≠ 1 := by
      intro h
      apply hk1
      apply Fin.ext
      simpa only [Fin.val_one] using h
    omega
  have hkhi : k.val + 2 ≤ N + 4 := by
    by_contra h
    apply hkLast
    apply Fin.ext
    change (k.val + 1 % (N + 4)) % (N + 4) = 0
    rw [Nat.mod_eq_of_lt (by omega : 1 < N + 4)]
    have heq : k.val + 1 = N + 4 := by have := k.isLt; omega
    rw [heq, Nat.mod_self]
  let m := k.val - 2
  let n := N + 4 - k.val - 2
  have hm : m + 2 = k.val := by dsimp [m]; omega
  have hsize : (m + 2) + (n + 2) = N + 4 := by dsimp [m, n]; omega
  let e := (finCongr hsize).trans (finCycle a)
  refine ⟨m, n, e, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [m]
    omega
  · dsimp [n]
    omega
  · intro i
    change finCycle a (finCongr hsize (finRotate _ i)) =
      finRotate _ (finCycle a (finCongr hsize i))
    rw [finCongr_rotate]
    simp only [finCycle_apply, finRotate_apply]
    ac_rfl
  · change finCongr hsize ((0 : Fin (m + 2)).castAdd (n + 2)) + a = a
    have hz : finCongr hsize ((0 : Fin (m + 2)).castAdd (n + 2)) = 0 := by
      apply Fin.ext
      rfl
    rw [hz, zero_add]
  · change finCongr hsize (Fin.natAdd (m + 2) (0 : Fin (n + 2))) + a = b
    have heq : finCongr hsize (Fin.natAdd (m + 2) (0 : Fin (n + 2))) = k := by
      apply Fin.ext
      change m + 2 + 0 = k.val
      omega
    rw [heq]
    exact sub_add_cancel b a
