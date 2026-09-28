import PoincareConjecture.Proofs.M65.Mathlib.GoodTimeGrid









set_option autoImplicit false

open Set
open scoped BigOperators

namespace PoincareConjecture.M65



noncomputable def delayedGridTime (a b step : ℝ) (n i : ℕ) : ℝ :=
  if i ≤ n + 2 then a + (i : ℝ) * step else b


theorem delayedGridTime_endpoints (a b step : ℝ) (n : ℕ) :
    delayedGridTime a b step n 0 = a ∧ delayedGridTime a b step n (n + 3) = b := by
  simp [delayedGridTime]


theorem delayedGridTime_mem {a b step : ℝ} {n : ℕ} (hstep : 0 ≤ step)
    (hend : a + ((n : ℝ) + 2) * step ≤ b) (i : ℕ) :
    delayedGridTime a b step n i ∈ Icc a b := by
  have hab : a ≤ b := by
    have hnonneg : 0 ≤ ((n : ℝ) + 2) * step := mul_nonneg (by positivity) hstep
    linarith
  by_cases hi : i ≤ n + 2
  · have hcast : (i : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast hi
    have hupper := mul_le_mul_of_nonneg_right hcast hstep
    have hlower := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hstep
    simp only [delayedGridTime, if_pos hi, mem_Icc]
    constructor <;> linarith
  · simpa only [delayedGridTime, if_neg hi, mem_Icc] using And.intro hab le_rfl



theorem delayedGridTime_ordered {a b step : ℝ} {n : ℕ} (hstep : 0 ≤ step)
    (hend : a + ((n : ℝ) + 2) * step ≤ b) {i : ℕ} (hi : i < n + 3) :
    delayedGridTime a b step n i ≤ delayedGridTime a b step n (i + 1) := by
  by_cases hsmall : i < n + 2
  · have his : i ≤ n + 2 := hsmall.le
    have hit : i + 1 ≤ n + 2 := Nat.succ_le_of_lt hsmall
    simp only [delayedGridTime, if_pos his, if_pos hit, Nat.cast_add, Nat.cast_one]
    linarith
  · have heq : i = n + 2 := by omega
    subst i
    simpa [delayedGridTime] using hend



theorem delayedGrid_badCell_sum (n : ℕ) (good : Finset ℕ) (step : ℝ) :
    (∑ i ∈ Finset.range (n + 2),
      if i ∈ good.image (fun j => j + 2) then 0 else step) =
        2 * step + ((Finset.range n \ good).card : ℝ) * step := by
  classical
  have hzero : 0 ∉ good.image (fun j => j + 2) := by simp
  have hone : 1 ∉ good.image (fun j => j + 2) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro j _
    omega
  have hshift (i : ℕ) : 2 + i ∈ good.image (fun j => j + 2) ↔ i ∈ good := by
    simp [Nat.add_comm]
  have hfilter : (Finset.range n).filter (fun i => i ∉ good) = Finset.range n \ good := by
    ext i
    simp
  have hsum : (∑ i ∈ Finset.range n, if i ∈ good then 0 else step) =
      ((Finset.range n \ good).card : ℝ) * step := by
    calc
      _ = ∑ i ∈ (Finset.range n).filter (fun i => i ∉ good), step := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ good <;> simp [hi]
      _ = _ := by rw [hfilter]; simp
  rw [show n + 2 = 2 + n by omega, Finset.sum_range_add]
  simp only [hshift, Finset.sum_range_succ, Finset.sum_range_zero,
    hzero, hone, if_false, zero_add]
  rw [hsum]
  ring



theorem delayedGrid_gap_sum (a b step : ℝ) (n : ℕ) (good : Finset ℕ)
    (hgood : good ⊆ Finset.range n) :
    (∑ i ∈ Finset.range (n + 3), if i ∈ good.image (fun j => j + 2) then 0
      else delayedGridTime a b step n (i + 1) - delayedGridTime a b step n i) =
        2 * step + ((Finset.range n \ good).card : ℝ) * step +
          (b - (a + ((n : ℝ) + 2) * step)) := by
  have hlast : n + 2 ∉ good.image (fun j => j + 2) := by
    intro hi
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hi
    have hjn := Finset.mem_range.mp (hgood hj)
    omega
  have hcell {i : ℕ} (hi : i ∈ Finset.range (n + 2)) :
      delayedGridTime a b step n (i + 1) - delayedGridTime a b step n i = step := by
    have his : i ≤ n + 2 := (Finset.mem_range.mp hi).le
    have hit : i + 1 ≤ n + 2 := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    simp only [delayedGridTime, if_pos his, if_pos hit, Nat.cast_add, Nat.cast_one]
    ring
  rw [show n + 3 = (n + 2) + 1 by omega, Finset.sum_range_succ]
  have hsum : (∑ i ∈ Finset.range (n + 2), if i ∈ good.image (fun j => j + 2) then 0
      else delayedGridTime a b step n (i + 1) - delayedGridTime a b step n i) =
        ∑ i ∈ Finset.range (n + 2), if i ∈ good.image (fun j => j + 2) then 0 else step :=
    Finset.sum_congr rfl (fun i hi => by rw [hcell hi])
  rw [hsum, delayedGrid_badCell_sum]
  simp [hlast, delayedGridTime]

end PoincareConjecture.M65
