import PoincareConjecture.Proofs.M47.BlowupControlsCapArrayContraction

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "Triple" => I × (I × I)
local notation "Tensor" => I → I → I → ℝ

noncomputable def capThreeTensorComponents (T : Tensor) : EuclideanSpace ℝ Triple :=
  WithLp.toLp 2 (fun p => T p.1 p.2.1 p.2.2)

theorem cap_threeTensor_norm_sq (T : Tensor) :
    ‖capThreeTensorComponents T‖ ^ 2 = ∑ i, ∑ j, ∑ k, T i j k ^ 2 := by
  simp only [capThreeTensorComponents, cap_array_norm_sq, Fintype.sum_prod_type]

theorem cap_threeTensor_cyclic_norm (T : Tensor) :
    ‖capThreeTensorComponents (fun i j k => T j k i)‖ = ‖capThreeTensorComponents T‖ := by
  let e : Triple ≃ Triple :=
    { toFun := fun p => (p.2.1, p.2.2, p.1)
      invFun := fun p => (p.2.2, p.1, p.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact cap_array_norm_reindex e (fun p => T p.1 p.2.1 p.2.2)

theorem cap_threeTensor_swap_norm (T : Tensor) :
    ‖capThreeTensorComponents (fun i j k => T j i k)‖ = ‖capThreeTensorComponents T‖ := by
  let e : Triple ≃ Triple :=
    { toFun := fun p => (p.2.1, p.1, p.2.2)
      invFun := fun p => (p.2.1, p.1, p.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact cap_array_norm_reindex e (fun p => T p.1 p.2.1 p.2.2)

theorem cap_threeTensor_left_pair_norm (T : Tensor) :
    ‖(WithLp.toLp 2 (fun p : (I × I) × I => T p.1.1 p.1.2 p.2) :
      EuclideanSpace ℝ ((I × I) × I))‖ = ‖capThreeTensorComponents T‖ := by
  exact cap_array_norm_reindex (Equiv.prodAssoc I I I) (fun p => T p.1 p.2.1 p.2.2)

theorem cap_threeTensor_trace_norm_le (T : Tensor) :
    ‖(WithLp.toLp 2 (fun j => ∑ i, T i i j) : EuclideanSpace ℝ I)‖ ≤
      Real.sqrt 3 * ‖capThreeTensorComponents T‖ := by
  have h := cap_array_trace_norm_le (fun j i k => T i k j)
  change _ ≤ Real.sqrt 3 * ‖capThreeTensorComponents (fun j i k => T i k j)‖ at h
  rwa [cap_threeTensor_cyclic_norm] at h

theorem cap_threeTensor_traced_contraction_abs_le
    (A : I → I → ℝ) (U S : Tensor) :
    |∑ i, ∑ j, ∑ k, ∑ l, A i j * U k k l * S l i j| ≤
      Real.sqrt 3 *
        ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2) : EuclideanSpace ℝ (I × I))‖ *
        ‖capThreeTensorComponents U‖ * ‖capThreeTensorComponents S‖ := by
  let t := fun l => ∑ k, U k k l
  have h := cap_array_pairing_abs_le (fun p : I × I => A p.1 p.2)
    (fun p : I × I => ∑ l, t l * S l p.1 p.2)
  have heq : (∑ p : I × I, A p.1 p.2 * ∑ l, t l * S l p.1 p.2) =
      ∑ i, ∑ j, ∑ k, ∑ l, A i j * U k k l * S l i j := by
    simp only [Fintype.sum_prod_type, t, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [heq] at h
  refine h.trans ?_
  have hc := cap_array_linear_combination_norm_le t (fun l (p : I × I) => S l p.1 p.2)
  have ht := cap_threeTensor_trace_norm_le U
  calc
    _ ≤ ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2) : EuclideanSpace ℝ (I × I))‖ *
        (‖(WithLp.toLp 2 t : EuclideanSpace ℝ I)‖ * ‖capThreeTensorComponents S‖) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ ≤ ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2) : EuclideanSpace ℝ (I × I))‖ *
        ((Real.sqrt 3 * ‖capThreeTensorComponents U‖) * ‖capThreeTensorComponents S‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem cap_threeTensor_cross_contraction_abs_le
    (A : I → I → ℝ) (U S : Tensor) :
    |∑ i, ∑ j, ∑ k, ∑ l, A i j * U i k l * S l k j| ≤
      ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2) : EuclideanSpace ℝ (I × I))‖ *
        ‖capThreeTensorComponents U‖ * ‖capThreeTensorComponents S‖ := by
  have h := cap_array_triangle_abs_le A (fun i (p : I × I) => U i p.1 p.2)
    (fun (p : I × I) j => S p.2 p.1 j)
  simp only [Fintype.sum_prod_type] at h
  have hs : ‖(WithLp.toLp 2 (fun p : (I × I) × I => S p.1.2 p.1.1 p.2) :
      EuclideanSpace ℝ ((I × I) × I))‖ = ‖capThreeTensorComponents S‖ := by
    exact (cap_threeTensor_left_pair_norm (fun i j k => S j i k)).trans
      (cap_threeTensor_swap_norm S)
  rw [hs] at h
  exact h

end PoincareConjecture.M47
