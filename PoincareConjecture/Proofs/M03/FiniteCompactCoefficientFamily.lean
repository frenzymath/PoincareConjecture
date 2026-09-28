import PoincareConjecture.Proofs.M03.CompactFiniteCoefficient

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M03



theorem exists_finite_compact_family_square_sum_bound
    {X I B M : Type*} [TopologicalSpace X]
    [Fintype I] [Fintype B]
    (s : Finset M) (K : M → Set X)
    (hK : ∀ a ∈ s, IsCompact (K a))
    (c : M → X → I → B → ℝ)
    (hc : ∀ a ∈ s, ∀ i b, ContinuousOn (fun x => c a x i b) (K a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ s, ∀ x ∈ K a, (∑ i, ∑ b, (c a x i b) ^ 2) ≤ C := by
  classical
  let D : M → ℝ := fun a =>
    if ha : a ∈ s then
      Classical.choose (exists_compact_finite_square_sum_bound
        (hK a ha) (fun x i b => c a x i b) (fun i b => hc a ha i b))
    else 0
  have hD (a : M) (ha : a ∈ s) :
      0 ≤ D a ∧ ∀ x ∈ K a, (∑ i, ∑ b, (c a x i b) ^ 2) ≤ D a := by
    dsimp [D]
    rw [dif_pos ha]
    exact Classical.choose_spec (exists_compact_finite_square_sum_bound
      (hK a ha) (fun x i b => c a x i b) (fun i b => hc a ha i b))
  let C : ℝ := s.sum D
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg (fun a ha => (hD a ha).1)
  refine ⟨C, hC, ?_⟩
  intro a ha x hx
  have hlocal := (hD a ha).2 x hx
  have hDa : D a ≤ s.sum D := by
    exact Finset.single_le_sum (fun b hb => (hD b hb).1) ha
  exact hlocal.trans (by simpa [C] using hDa)

end PoincareConjecture.Proofs.M03
