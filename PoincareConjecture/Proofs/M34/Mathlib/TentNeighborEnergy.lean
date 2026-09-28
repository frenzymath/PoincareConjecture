import PoincareConjecture.Proofs.M34.Mathlib.FiniteNeighborEnergy
import Mathlib.Data.Nat.Dist











set_option autoImplicit false

open scoped BigOperators



theorem dyadic_nat_dist_adjacent_bounds (j i : ℕ) :
    (1 / 2 : ℝ) ^ Nat.dist (i + 1) j ≤ 2 * (1 / 2 : ℝ) ^ Nat.dist i j ∧
    (1 / 2 : ℝ) ^ Nat.dist i j ≤ 2 * (1 / 2 : ℝ) ^ Nat.dist (i + 1) j := by
  have h₀ : Nat.dist i j ≤ Nat.dist (i + 1) j + 1 := by simp only [Nat.dist]; omega
  have h₁ : Nat.dist (i + 1) j ≤ Nat.dist i j + 1 := by simp only [Nat.dist]; omega
  have hq₀ := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) h₀
  have hq₁ := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) h₁
  simp only [pow_succ] at hq₀ hq₁
  constructor <;> linarith




theorem weighted_neighbor_sum_range_le_nine {E R w : ℕ → ℝ} {C : ℝ}
    (hn : ∀ i, 0 ≤ E i) (hw : ∀ i, 0 ≤ w i)
    (hwr : ∀ i, w (i + 1) ≤ 2 * w i ∧ w i ≤ 2 * w (i + 1))
    (hC : 0 ≤ C) (hzero : R 0 ≤ 0)
    (hr : ∀ n, R (n + 1) ≤ C * (E n + E (n + 1) + E (n + 2))) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 3), w i * R i) ≤
      9 * C * (∑ i ∈ Finset.range (k + 3), w i * E i) +
        2 * C * (w (k + 3) * E (k + 3)) := by
  let a := fun i => w i * E i
  let b := fun i => w i * R i
  have ha (i) : 0 ≤ a i := mul_nonneg (hw i) (hn i)
  have h0 : b 0 ≤ C * (a 0 + 2 * a 1 + 2 ^ 2 * a 2) := by
    have hz : b 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hw 0) hzero
    exact hz.trans (mul_nonneg hC (by nlinarith [ha 0, ha 1, ha 2]))
  have hrow (n) : b (n + 1) ≤ C * (2 * a n + a (n + 1) + 2 * a (n + 2)) := by
    calc
      b (n + 1) ≤ w (n + 1) * (C * (E n + E (n + 1) + E (n + 2))) :=
        mul_le_mul_of_nonneg_left (hr n) (hw (n + 1))
      _ = C * (w (n + 1) * E n + w (n + 1) * E (n + 1) + w (n + 1) * E (n + 2)) :=
        by ring
      _ ≤ C * ((2 * w n) * E n + w (n + 1) * E (n + 1) + (2 * w (n + 2)) * E (n + 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_right (hwr n).1 (hn n)) le_rfl)
          (mul_le_mul_of_nonneg_right (hwr (n + 1)).2 (hn (n + 2)))) hC
      _ = _ := by dsimp only [a]; ring
  have h1 : b 1 ≤ C * (2 * a 0 + a 1 + 2 * a 2) := hrow 0
  have htail (n) : b (n + 2) ≤ C * (2 * a (n + 1) + a (n + 2) + 2 * a (n + 3)) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hrow (n + 1)
  have hh := sum_range_le_of_boundary_neighbor_bounds h0 h1 htail k
  let A := ∑ i ∈ Finset.range (k + 3), a i
  have htwo : a 2 ≤ A := Finset.single_le_sum (fun i _ => ha i)
    (Finset.mem_range.mpr (by omega))
  have hinter : (2 + 1 + 2) * A - 2 * a 0 + 2 ^ 2 * a 2 -
      2 * a (k + 2) + 2 * a (k + 3) ≤ 9 * A + 2 * a (k + 3) := by
    nlinarith [ha 0, ha (k + 2)]
  exact hh.trans ((mul_le_mul_of_nonneg_left hinter hC).trans_eq (by ring))
