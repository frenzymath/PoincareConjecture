import PoincareConjecture.Proofs.M03.ScalarEnergyComparison









set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M03

theorem sum_sq_linear_combination_le
    {I B : Type*} [Fintype I] [Fintype B]
    (c : I → B → ℝ) (x : B → ℝ) :
    (∑ i, (∑ b, c i b * x b) ^ 2) ≤
      (∑ i, ∑ b, (c i b) ^ 2) * (∑ b, (x b) ^ 2) := by
  calc
    (∑ i, (∑ b, c i b * x b) ^ 2) ≤
        ∑ i, (∑ b, (c i b) ^ 2) * (∑ b, (x b) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_comm] using
        (Finset.sum_mul_sq_le_sq_mul_sq
          (s := Finset.univ) (f := fun b => c i b) (g := fun b => x b))
    _ = (∑ i, ∑ b, (c i b) ^ 2) * (∑ b, (x b) ^ 2) := by
      rw [← Finset.sum_mul]

theorem sum_two_mul_linear_combination_le
    {I B : Type*} [Fintype I] [Fintype B]
    (c : I → B → ℝ) (a : I → ℝ) (x : B → ℝ)
    {ε C : ℝ} (hε : 0 < ε)
    (hc : (∑ i, ∑ b, (c i b) ^ 2) ≤ C)
    (hC : 0 ≤ C) :
    (∑ i, 2 * a i * (∑ b, c i b * x b)) ≤
      ε * (∑ b, (x b) ^ 2) + (C / ε) * (∑ i, (a i) ^ 2) := by
  let A₂ : ℝ := ∑ i, (a i) ^ 2
  let X₂ : ℝ := ∑ b, (x b) ^ 2
  let P : ℝ := ∑ i, a i * (∑ b, c i b * x b)
  have hA : 0 ≤ A₂ := by
    dsimp [A₂]
    positivity
  have hX : 0 ≤ X₂ := by
    dsimp [X₂]
    positivity
  have hcross : P ^ 2 ≤ A₂ * (∑ i, (∑ b, c i b * x b) ^ 2) := by
    simpa only [mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (s := Finset.univ) (f := fun i => a i)
        (g := fun i => ∑ b, c i b * x b))
  have hcoeff : (∑ i, (∑ b, c i b * x b) ^ 2) ≤ C * X₂ := by
    exact (sum_sq_linear_combination_le c x).trans
      (mul_le_mul_of_nonneg_right hc hX)
  have hP : 2 * P ≤ ε * X₂ + (C / ε) * A₂ := by
    by_cases hX0 : X₂ = 0
    · have hsum : ∑ i, (∑ b, c i b * x b) ^ 2 = 0 := by
        have hcoeff0 := hcoeff
        simp [hX0] at hcoeff0
        exact le_antisymm hcoeff0 (by positivity)
      have hP0 : P = 0 := by
        have hzero : ∀ i, (∑ b, c i b * x b) = 0 := by
          intro i
          have hi := (Finset.sum_eq_zero_iff_of_nonneg
            (s := Finset.univ)
            (fun k _ => sq_nonneg (∑ b, c k b * x b))).mp hsum
          exact sq_eq_zero_iff.mp (hi i (Finset.mem_univ i))
        simp [P, hzero]
      simp [hX0, hP0]
      exact mul_nonneg (div_nonneg hC (le_of_lt hε)) hA
    · have hXpos : 0 < X₂ := lt_of_le_of_ne hX (Ne.symm hX0)
      have hYoung : 2 * P ≤ ε * X₂ + P ^ 2 / (ε * X₂) := by
        have hsquare := sq_nonneg (ε * X₂ - P)
        field_simp
        nlinarith
      have hquot : P ^ 2 / (ε * X₂) ≤ (C / ε) * A₂ := by
        apply (div_le_iff₀ (mul_pos hε hXpos)).mpr
        calc
          P ^ 2 ≤ A₂ * (∑ i, (∑ b, c i b * x b) ^ 2) := hcross
          _ ≤ A₂ * (C * X₂) :=
            mul_le_mul_of_nonneg_left hcoeff hA
          _ = (C / ε) * A₂ * (ε * X₂) := by field_simp
      exact hYoung.trans (by nlinarith [hquot])
  simpa [A₂, X₂, P, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hP

end PoincareConjecture.Proofs.M03
