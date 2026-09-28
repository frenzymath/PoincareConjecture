import PoincareConjecture.Proofs.M47.BlowupControlsCapThreeArrays

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "Tensor" => I → I → I → ℝ

theorem cap_quadratic_scalar_contraction_le
    (A : I → I → ℝ) (U S B : Tensor) {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hA : ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2) :
      EuclideanSpace ℝ (I × I))‖ ≤ Real.sqrt 3 * a)
    (hU : ‖capThreeTensorComponents U‖ ≤ a ^ 2 * y)
    (hS : ‖capThreeTensorComponents S‖ ≤ 3 * y)
    (hB : ‖capThreeTensorComponents B‖ ≤ (3 / 2 : ℝ) * a * y) :
    |(1 / 2 : ℝ) *
        ((∑ i, ∑ j, ∑ k, ∑ l, A i j * U k k l * S l i j) -
          (∑ i, ∑ j, ∑ k, ∑ l, A i j * U i k l * S l k j)) +
      ((∑ i, ∑ j, ∑ k, ∑ l, A i j * B k k l * B l i j) -
        (∑ i, ∑ j, ∑ k, ∑ l, A i j * B k i l * B l k j))| ≤
      18 * a ^ 3 * y ^ 2 := by
  let NA := ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2) :
    EuclideanSpace ℝ (I × I))‖
  let NU := ‖capThreeTensorComponents U‖
  let NS := ‖capThreeTensorComponents S‖
  let NB := ‖capThreeTensorComponents B‖
  let q1 := ∑ i, ∑ j, ∑ k, ∑ l, A i j * U k k l * S l i j
  let q2 := ∑ i, ∑ j, ∑ k, ∑ l, A i j * U i k l * S l k j
  let q3 := ∑ i, ∑ j, ∑ k, ∑ l, A i j * B k k l * B l i j
  let q4 := ∑ i, ∑ j, ∑ k, ∑ l, A i j * B k i l * B l k j
  have h1 : |q1| ≤ Real.sqrt 3 * NA * NU * NS :=
    cap_threeTensor_traced_contraction_abs_le A U S
  have h2 : |q2| ≤ NA * NU * NS := cap_threeTensor_cross_contraction_abs_le A U S
  have h3 : |q3| ≤ Real.sqrt 3 * NA * NB * NB :=
    cap_threeTensor_traced_contraction_abs_le A B B
  have h4 : |q4| ≤ NA * NB * NB := by
    have h := cap_threeTensor_cross_contraction_abs_le A (fun i k l => B k i l) B
    rw [cap_threeTensor_swap_norm] at h
    exact h
  have hN : 0 ≤ NU * NS / 2 + NB ^ 2 := by
    dsimp only [NU, NS, NB]
    positivity
  have hUS : NU * NS ≤ (a ^ 2 * y) * (3 * y) :=
    mul_le_mul hU hS (norm_nonneg _) (by positivity)
  have hBs : NB ^ 2 ≤ ((3 / 2 : ℝ) * a * y) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hB
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsbound : Real.sqrt 3 ≤ (9 / 5 : ℝ) := by nlinarith
  change |(1 / 2 : ℝ) * (q1 - q2) + (q3 - q4)| ≤ _
  calc
    _ ≤ (1 / 2 : ℝ) * (|q1| + |q2|) + (|q3| + |q4|) := by
      calc
        _ ≤ |(1 / 2 : ℝ) * (q1 - q2)| + |q3 - q4| := abs_add_le _ _
        _ = (1 / 2 : ℝ) * |q1 - q2| + |q3 - q4| := by rw [abs_mul]; norm_num
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (abs_sub q1 q2) (by norm_num)) (abs_sub q3 q4)
    _ ≤ (Real.sqrt 3 + 1) * NA * (NU * NS / 2 + NB ^ 2) := by
      nlinarith only [h1, h2, h3, h4]
    _ ≤ (Real.sqrt 3 + 1) * (Real.sqrt 3 * a) *
        (NU * NS / 2 + NB ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA (by positivity)) hN
    _ ≤ (Real.sqrt 3 + 1) * (Real.sqrt 3 * a) *
        (((a ^ 2 * y) * (3 * y)) / 2 + ((3 / 2 : ℝ) * a * y) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add (div_le_div_of_nonneg_right hUS (by norm_num)) hBs)
        (by positivity)
    _ = ((3 + Real.sqrt 3) * (15 / 4 : ℝ)) * (a ^ 3 * y ^ 2) := by
      ring_nf
      rw [hs2]
      ring
    _ ≤ 18 * (a ^ 3 * y ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith only [hsbound]
    _ = _ := by ring

end PoincareConjecture.M47
