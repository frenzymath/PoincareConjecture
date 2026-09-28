import PoincareConjecture.Proofs.M03.RateFiniteAlgebra

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M03

theorem exists_compact_finite_square_sum_bound
    {X I B : Type*} [TopologicalSpace X] [Fintype I] [Fintype B]
    {K : Set X} (hK : IsCompact K)
    (c : X → I → B → ℝ)
    (hc : ∀ i b, ContinuousOn (fun x => c x i b) K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, (∑ i, ∑ b, (c x i b) ^ 2) ≤ C := by
  let S : X → ℝ := fun x => ∑ i, ∑ b, (c x i b) ^ 2
  have hS : ContinuousOn S K := by
    unfold S
    apply continuousOn_finsetSum
    intro i hi
    apply continuousOn_finsetSum
    intro b hb
    exact (hc i b).pow 2
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hS
  refine ⟨max C₀ 0, le_max_right C₀ 0, ?_⟩
  intro x hx
  have hnorm : ‖S x‖ ≤ max C₀ 0 :=
    (hC₀ x hx).trans (le_max_left C₀ 0)
  exact (le_abs_self (S x)).trans hnorm

end PoincareConjecture.Proofs.M03
