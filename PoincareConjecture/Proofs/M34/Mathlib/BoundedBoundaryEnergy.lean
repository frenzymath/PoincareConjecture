import PoincareConjecture.Proofs.M34.Mathlib.BoundaryEnergyDecay

set_option autoImplicit false

open Set

theorem le_geometric_exp_of_bounded_boundary_energy
    {E : ℕ → ℝ → ℝ} {a b C M : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i, ContinuousOn (E (i + 1)) (Icc a b))
    (hd : ∀ i t, t ∈ Ioo a b → DifferentiableAt ℝ (E (i + 1)) t)
    (hinit : ∀ i, E (i + 1) a = 0)
    (hn : ∀ i t, t ∈ Icc a b → 0 ≤ E (i + 1) t)
    (hb : ∀ i t, t ∈ Icc a b → E i t ≤ M)
    (hr : ∀ n t, t ∈ Ioo a b →
      deriv (E (n + 1)) t ≤ C * (E n t + E (n + 1) t + E (n + 2) t)) :
    ∀ j t, t ∈ Icc a b →
      E (j + 1) t ≤ M * (1 / 2 : ℝ) ^ (j + 1) * Real.exp (9 * C * (t - a)) := by
  let A : ℕ → ℝ → ℝ := fun i => if i = 0 then fun _ => M else E i
  have hAc (i) : ContinuousOn (A i) (Icc a b) := by
    cases i with
    | zero => exact continuousOn_const
    | succ i => simpa only [A, Nat.succ_ne_zero, if_false] using hc i
  have hAd (i) (t) (ht : t ∈ Ioo a b) : DifferentiableAt ℝ (A i) t := by
    cases i with
    | zero => exact differentiableAt_const M
    | succ i => simpa only [A, Nat.succ_ne_zero, if_false] using hd i t ht
  have hAn (i) (t) (ht : t ∈ Icc a b) : 0 ≤ A i t := by
    cases i with
    | zero => exact (hn 0 t ht).trans (hb 1 t ht)
    | succ i => simpa only [A, Nat.succ_ne_zero, if_false] using hn i t ht
  have hAb (i) (t) (ht : t ∈ Icc a b) : A i t ≤ M := by
    by_cases hi : i = 0
    · simp only [A, hi, if_pos rfl, le_refl]
    · simpa only [A, if_neg hi] using hb i t ht
  have hAr (n) (t) (ht : t ∈ Ioo a b) :
      deriv (A (n + 1)) t ≤ C * (A n t + A (n + 1) t + A (n + 2) t) := by
    by_cases hn0 : n = 0
    · subst n
      simp only [A, Nat.reduceAdd, Nat.reduceEqDiff, if_false, if_pos rfl]
      exact (hr 0 t ht).trans (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (hb 0 t ⟨ht.1.le, ht.2.le⟩) le_rfl) le_rfl) hC)
    · simpa only [A, if_neg hn0, Nat.add_eq_zero_iff, Nat.one_ne_zero, Nat.reduceEqDiff,
        and_false, if_false] using hr n t ht
  have hAinit (i) : A i a = if i = 0 then M else 0 := by
    cases i with
    | zero => rfl
    | succ i => simpa only [A, Nat.succ_ne_zero, if_false] using hinit i
  have h := le_geometric_exp_of_bounded_neighbor_energy_rates hC hAc hAd
    hAinit hAn hAb
    (fun t _ => by simp [A]) hAr
  intro j t ht
  simpa only [A, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false] using h (j + 1) t ht
