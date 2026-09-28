import PoincareConjecture.Proofs.M03.RateFiniteAlgebra

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M03



theorem sum_two_mul_nested_linear_combination_le
    {I L J K : Type*} [Fintype I] [Fintype L] [Fintype J] [Fintype K]
    (c : I → L → J → K → ℝ) (a : I → ℝ)
    (x : L → J → K → ℝ)
    {ε C : ℝ} (hε : 0 < ε)
    (hc : (∑ i, ∑ l, ∑ j, ∑ k, (c i l j k) ^ 2) ≤ C)
    (hC : 0 ≤ C) :
    (∑ i, 2 * a i * (∑ l, ∑ j, ∑ k, c i l j k * x l j k)) ≤
      ε * (∑ l, ∑ j, ∑ k, (x l j k) ^ 2) +
        (C / ε) * (∑ i, (a i) ^ 2) := by
  let B := L × J × K
  let c' : I → B → ℝ := fun i p => c i p.1 p.2.1 p.2.2
  let x' : B → ℝ := fun p => x p.1 p.2.1 p.2.2
  have hc' : (∑ i, ∑ p, (c' i p) ^ 2) ≤ C := by
    simpa [B, c', Fintype.sum_prod_type, Finset.sum_mul,
      Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm] using hc
  have hpacked := sum_two_mul_linear_combination_le c' a x' hε hc' hC
  simpa [B, c', x', Fintype.sum_prod_type, Finset.sum_mul,
    Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm] using hpacked

end PoincareConjecture.Proofs.M03
