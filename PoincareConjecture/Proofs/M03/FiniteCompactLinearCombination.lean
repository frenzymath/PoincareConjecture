import PoincareConjecture.Proofs.M03.FiniteCompactCoefficientFamily

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M03



theorem exists_finite_compact_family_linear_combination_bound
    {X I B M : Type*} [TopologicalSpace X]
    [Fintype I] [Fintype B]
    (s : Finset M) (K : M → Set X)
    (hK : ∀ a ∈ s, IsCompact (K a))
    (c : M → X → I → B → ℝ)
    (hc : ∀ a ∈ s, ∀ i b, ContinuousOn (fun x => c a x i b) (K a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ s, ∀ x ∈ K a, ∀ v : B → ℝ,
        (∑ i, (∑ b, c a x i b * v b) ^ 2) ≤
          C * (∑ b, (v b) ^ 2) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_finite_compact_family_square_sum_bound s K hK c hc
  refine ⟨C, hC, ?_⟩
  intro a ha x hx v
  exact (sum_sq_linear_combination_le (fun i b => c a x i b) v).trans
    (mul_le_mul_of_nonneg_right (hcoeff a ha x hx)
      (by positivity))

end PoincareConjecture.Proofs.M03
