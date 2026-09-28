import PoincareConjecture.Proofs.M03.FiniteCompactCoefficientFamily

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M03

theorem exists_finite_compact_family_four_array_square_sum_bound
    {X I D H A S M : Type*} [TopologicalSpace X]
    [Fintype I] [Fintype D] [Fintype H] [Fintype A] [Fintype S]
    (s : Finset M) (K : M → Set X)
    (hK : ∀ a ∈ s, IsCompact (K a))
    (cD : M → X → I → D → ℝ)
    (cH : M → X → I → H → ℝ)
    (cA : M → X → I → A → ℝ)
    (cS : M → X → I → S → ℝ)
    (hcD : ∀ a ∈ s, ∀ i d, ContinuousOn (fun x => cD a x i d) (K a))
    (hcH : ∀ a ∈ s, ∀ i h, ContinuousOn (fun x => cH a x i h) (K a))
    (hcA : ∀ a ∈ s, ∀ i j, ContinuousOn (fun x => cA a x i j) (K a))
    (hcS : ∀ a ∈ s, ∀ i k, ContinuousOn (fun x => cS a x i k) (K a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ s, ∀ x ∈ K a,
        (∑ i, ∑ d, (cD a x i d) ^ 2) +
          (∑ i, ∑ h, (cH a x i h) ^ 2) +
            (∑ i, ∑ j, (cA a x i j) ^ 2) +
              (∑ i, ∑ k, (cS a x i k) ^ 2) ≤ C := by
  let B := D ⊕ (H ⊕ (A ⊕ S))
  let c : M → X → I → B → ℝ := fun a x i q =>
    Sum.elim (cD a x i) (Sum.elim (cH a x i) (Sum.elim (cA a x i) (cS a x i))) q
  have hc : ∀ a ∈ s, ∀ i b, ContinuousOn (fun x => c a x i b) (K a) := by
    intro a ha i b
    cases b with
    | inl d =>
        simpa [c] using hcD a ha i d
    | inr b =>
        cases b with
        | inl h =>
            simpa [c] using hcH a ha i h
        | inr b =>
            cases b with
            | inl j =>
                simpa [c] using hcA a ha i j
            | inr k =>
                simpa [c] using hcS a ha i k
  obtain ⟨C, hC, hbound⟩ :=
    exists_finite_compact_family_square_sum_bound s K hK c hc
  refine ⟨C, hC, ?_⟩
  intro a ha x hx
  have hpacked := hbound a ha x hx
  simpa [B, c, Fintype.sum_sum_type, Finset.sum_add_distrib,
    add_assoc, add_left_comm, add_comm] using hpacked

end PoincareConjecture.Proofs.M03
