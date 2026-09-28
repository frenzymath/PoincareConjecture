import PoincareConjecture.Proofs.M34.Mathlib.NeighborEnergySum

set_option autoImplicit false

open scoped BigOperators

theorem sum_range_le_of_boundary_neighbor_bounds {a b : ℕ → ℝ} {C q r : ℝ}
    (hzero : b 0 ≤ C * (a 0 + r * a 1 + r ^ 2 * a 2))
    (hone : b 1 ≤ C * (q * a 0 + a 1 + r * a 2))
    (htail : ∀ n, b (n + 2) ≤ C * (q * a (n + 1) + a (n + 2) + r * a (n + 3)))
    (k : ℕ) :
    (∑ i ∈ Finset.range (k + 3), b i) ≤ C *
      ((q + 1 + r) * (∑ i ∈ Finset.range (k + 3), a i) - r * a 0 + r ^ 2 * a 2 -
        q * a (k + 2) + r * a (k + 3)) := by
  induction k with
  | zero =>
    have hh := add_le_add (add_le_add hzero hone) (htail 0)
    norm_num only [Nat.zero_add] at hh ⊢
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    convert hh using 1
    · rfl
    · ring
  | succ k ih =>
    have hrow : b (k + 3) ≤ C * (q * a (k + 2) + a (k + 3) + r * a (k + 4)) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using htail (k + 1)
    have hsumB : (∑ i ∈ Finset.range (k + 1 + 3), b i) =
        (∑ i ∈ Finset.range (k + 3), b i) + b (k + 3) := by
      rw [show k + 1 + 3 = k + 3 + 1 by omega, Finset.sum_range_succ]
    have hsumA : (∑ i ∈ Finset.range (k + 1 + 3), a i) =
        (∑ i ∈ Finset.range (k + 3), a i) + a (k + 3) := by
      rw [show k + 1 + 3 = k + 3 + 1 by omega, Finset.sum_range_succ]
    rw [hsumB, hsumA]
    convert add_le_add ih hrow using 1
    · rfl
    · simp only [Nat.add_assoc, Nat.reduceAdd]
      ring

theorem geometric_weighted_neighbor_sum_range_le {E R : ℕ → ℝ} {C : ℝ}
    (hn : ∀ i, 0 ≤ E i) (hC : 0 ≤ C)
    (hzero : R 0 ≤ C * (E 0 + E 1 + E 2))
    (hone : R 1 ≤ C * (E 0 + E 1 + E 2))
    (htail : ∀ n, R (n + 2) ≤ C * (E (n + 1) + E (n + 2) + E (n + 3)))
    (k : ℕ) :
    (∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i * R i) ≤
      8 * C * (∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i * E i) +
        2 * C * ((1 / 2 : ℝ) ^ (k + 3) * E (k + 3)) := by
  let a := fun i => (1 / 2 : ℝ) ^ i * E i
  let b := fun i => (1 / 2 : ℝ) ^ i * R i
  have ha (i) : 0 ≤ a i := mul_nonneg (pow_nonneg (by norm_num) _) (hn i)
  have h0 : b 0 ≤ C * (a 0 + 2 * a 1 + 2 ^ 2 * a 2) := by
    calc
      b 0 = R 0 := by simp [b]
      _ ≤ C * (E 0 + E 1 + E 2) := hzero
      _ = C * (a 0 + 2 * a 1 + 2 ^ 2 * a 2) := by dsimp [a]; ring
  have h1 : b 1 ≤ C * ((1 / 2) * a 0 + a 1 + 2 * a 2) := by
    calc
      b 1 = (1 / 2) * R 1 := by simp [b]
      _ ≤ (1 / 2) * (C * (E 0 + E 1 + E 2)) :=
        mul_le_mul_of_nonneg_left hone (by norm_num)
      _ = C * ((1 / 2) * a 0 + a 1 + 2 * a 2) := by dsimp [a]; ring
  have ht (n : ℕ) : b (n + 2) ≤ C * ((1 / 2) * a (n + 1) + a (n + 2) + 2 * a (n + 3)) := by
    calc
      b (n + 2) ≤ (1 / 2 : ℝ) ^ (n + 2) *
          (C * (E (n + 1) + E (n + 2) + E (n + 3))) :=
        mul_le_mul_of_nonneg_left (htail n) (pow_nonneg (by norm_num) _)
      _ = _ := by dsimp [a]; simp only [pow_add]; ring
  have hh := sum_range_le_of_boundary_neighbor_bounds h0 h1 ht k
  let A := ∑ i ∈ Finset.range (k + 3), a i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  have htwo : a 2 ≤ A := Finset.single_le_sum (fun i _ => ha i)
    (Finset.mem_range.mpr (by omega))
  have hinter : ((1 / 2 : ℝ) + 1 + 2) * A - 2 * a 0 + 2 ^ 2 * a 2 -
      (1 / 2) * a (k + 2) + 2 * a (k + 3) ≤ 8 * A + 2 * a (k + 3) := by
    nlinarith [ha 0, ha (k + 2)]
  exact hh.trans ((mul_le_mul_of_nonneg_left hinter hC).trans_eq (by ring))
