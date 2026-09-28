import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring











set_option autoImplicit false

open scoped BigOperators



theorem tsum_le_of_boundary_neighbor_bounds {a b : ℕ → ℝ} {C q r : ℝ}
    (ha : Summable a) (hb : Summable b) (hn : ∀ i, 0 ≤ a i) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hzero : b 0 ≤ C * (a 0 + r * a 1 + r ^ 2 * a 2))
    (hone : b 1 ≤ C * (q * a 0 + a 1 + r * a 2))
    (htail : ∀ n, b (n + 2) ≤ C * (q * a (n + 1) + a (n + 2) + r * a (n + 3))) :
    (∑' i, b i) ≤ C * (q + 1 + r + r ^ 2) * (∑' i, a i) := by
  have ha1 : Summable (fun n => a (n + 1)) := (summable_nat_add_iff 1).2 ha
  have ha2 : Summable (fun n => a (n + 2)) := (summable_nat_add_iff 2).2 ha
  have ha3 : Summable (fun n => a (n + 3)) := (summable_nat_add_iff 3).2 ha
  have hb2 : Summable (fun n => b (n + 2)) := (summable_nat_add_iff 2).2 hb
  have hs := ((ha1.mul_left q).add ha2).add (ha3.mul_left r)
  have ht := Summable.tsum_le_tsum htail hb2 (hs.mul_left C)
  rw [hs.tsum_mul_left C, ((ha1.mul_left q).add ha2).tsum_add (ha3.mul_left r),
    (ha1.mul_left q).tsum_add ha2, ha1.tsum_mul_left q, ha3.tsum_mul_left r] at ht
  let A := ∑' i, a i
  have hp1 := ha.sum_add_tsum_nat_add 1
  have hp2 := ha.sum_add_tsum_nat_add 2
  have hp3 := ha.sum_add_tsum_nat_add 3
  have hpb := hb.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at hp1 hp2 hp3 hpb
  have he1 : (∑' n, a (n + 1)) = A - a 0 := by dsimp [A]; linarith
  have he2 : (∑' n, a (n + 2)) = A - a 0 - a 1 := by dsimp [A]; linarith
  have he3 : (∑' n, a (n + 3)) = A - a 0 - a 1 - a 2 := by dsimp [A]; linarith
  rw [he1, he2, he3] at ht
  have htwo : a 2 ≤ A := ha.le_tsum 2 (fun i _ => hn i)
  calc
    (∑' i, b i) = b 0 + b 1 + ∑' n, b (n + 2) := hpb.symm
    _ ≤ C * (a 0 + r * a 1 + r ^ 2 * a 2) +
        C * (q * a 0 + a 1 + r * a 2) +
        C * (q * (A - a 0) + (A - a 0 - a 1) + r * (A - a 0 - a 1 - a 2)) :=
      add_le_add (add_le_add hzero hone) ht
    _ = C * ((q + 1 + r) * A - r * a 0 + r ^ 2 * a 2) := by ring
    _ ≤ C * ((q + 1 + r) * A + r ^ 2 * A) := by
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith [mul_nonneg hr (hn 0), mul_le_mul_of_nonneg_left htwo (sq_nonneg r)]
    _ = C * (q + 1 + r + r ^ 2) * A := by ring



theorem geometric_weighted_neighbor_sum_le {E R : ℕ → ℝ} {C : ℝ}
    (hE : Summable (fun i => (1 / 2 : ℝ) ^ i * E i))
    (hR : Summable (fun i => (1 / 2 : ℝ) ^ i * R i))
    (hn : ∀ i, 0 ≤ E i) (hC : 0 ≤ C)
    (hzero : R 0 ≤ C * (E 0 + E 1 + E 2))
    (hone : R 1 ≤ C * (E 0 + E 1 + E 2))
    (htail : ∀ n, R (n + 2) ≤ C * (E (n + 1) + E (n + 2) + E (n + 3))) :
    (∑' i, (1 / 2 : ℝ) ^ i * R i) ≤ 8 * C * (∑' i, (1 / 2 : ℝ) ^ i * E i) := by
  let a := fun i => (1 / 2 : ℝ) ^ i * E i
  let b := fun i => (1 / 2 : ℝ) ^ i * R i
  have han : ∀ i, 0 ≤ a i := fun i => mul_nonneg (pow_nonneg (by norm_num) _) (hn i)
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
      _ = C * ((1 / 2) * a (n + 1) + a (n + 2) + 2 * a (n + 3)) := by
        dsimp [a]
        simp only [pow_add]
        ring
  have hsum := tsum_le_of_boundary_neighbor_bounds hE hR han hC (by norm_num) h0 h1 ht
  have hnonneg : 0 ≤ C * (∑' i, a i) := mul_nonneg hC (tsum_nonneg han)
  change (∑' i, b i) ≤ 8 * C * (∑' i, a i)
  change (∑' i, b i) ≤ C * ((1 / 2) + 1 + 2 + 2 ^ 2) * (∑' i, a i) at hsum
  nlinarith
