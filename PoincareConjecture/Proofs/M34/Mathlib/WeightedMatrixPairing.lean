import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

theorem weighted_matrix_pairing_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → ℝ) (e : κ → ℝ) (hd : ∀ i, 0 < d i) (he : ∀ j, 0 < e j)
    (A : ι → κ → ℝ) (v : ι → ℝ) (w : κ → ℝ) :
    (∑ i, ∑ j, A i j * v i * w j) ^ 2 ≤
      (∑ i, ∑ j, (d i)⁻¹ * (e j)⁻¹ * A i j ^ 2) *
        (∑ i, d i * v i ^ 2) * (∑ j, e j * w j ^ 2) := by
  classical
  let f (p : ι × κ) := A p.1 p.2 / Real.sqrt (d p.1 * e p.2)
  let g (p : ι × κ) := Real.sqrt (d p.1 * e p.2) * v p.1 * w p.2
  have hpair (i : ι) (j : κ) : f (i, j) * g (i, j) = A i j * v i * w j := by
    dsimp [f, g]
    have hs : Real.sqrt (d i * e j) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (mul_pos (hd i) (he j)))
    field_simp
  have hf (i : ι) (j : κ) : f (i, j) ^ 2 = (d i)⁻¹ * (e j)⁻¹ * A i j ^ 2 := by
    dsimp [f]
    rw [div_pow, Real.sq_sqrt (mul_pos (hd i) (he j)).le]
    field_simp
  have hg (i : ι) (j : κ) : g (i, j) ^ 2 = (d i * v i ^ 2) * (e j * w j ^ 2) := by
    dsimp [g]
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_pos (hd i) (he j)).le]
    ring
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simp only [Fintype.sum_prod_type, hpair, hf, hg] at h
  rw [← Finset.sum_mul_sum] at h
  simpa only [mul_assoc] using h

theorem abs_matrix_quadratic_le_of_weighted_sq
    {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (A : ι → ι → ℝ) (v : ι → ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hA : (∑ i, ∑ j, (d i)⁻¹ * (d j)⁻¹ * A i j ^ 2) ≤ epsilon ^ 2) :
    |∑ i, ∑ j, A i j * v i * v j| ≤ epsilon * ∑ i, d i * v i ^ 2 := by
  have hQ : 0 ≤ ∑ i, d i * v i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i).le (sq_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hepsilon hQ)).mp
  rw [sq_abs]
  calc
    _ ≤ (∑ i, ∑ j, (d i)⁻¹ * (d j)⁻¹ * A i j ^ 2) *
        (∑ i, d i * v i ^ 2) ^ 2 := by
      simpa only [pow_two, mul_assoc] using weighted_matrix_pairing_sq_le d d hd hd A v v
    _ ≤ epsilon ^ 2 * (∑ i, d i * v i ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    _ = (epsilon * ∑ i, d i * v i ^ 2) ^ 2 := by ring
