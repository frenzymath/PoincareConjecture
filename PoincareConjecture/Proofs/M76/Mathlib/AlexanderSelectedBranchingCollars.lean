import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBranchingPoint
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderCollarWidthRestriction












set_option autoImplicit false

open Set

namespace Geometry

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]







theorem exists_selected_child_branching_collars
    {S s T : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (hs : s ⊆ S) (hsection : T ∩ {x | A x = 0} ⊆ s ∩ {x | A x = 0})
    (hcollars : q ∈ s →
      Nonempty (AlexanderCollarSlab T A q β) ∧
      Nonempty (AlexanderCollarSlab T (-A) q γ))
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hfull : S ∩ {x | A x = 0} = ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    {a : ℕ} (hchild : HasAlexanderCurvePresentation (T ∩ {x | A x = 0}) a)
    (ha : a ≠ 0) :
    ∃ (m : ℕ) (N : Fin m → ℕ) (Q : ∀ i, Polygon E (N i + 3)),
      0 < m ∧
      (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges) ∧
      T ∩ {x | A x = 0} = ⋃ i, (Q i).boundary ℝ ∧
      Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ {q}) ∧
      (¬ Pairwise (fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ))) ∧
      alexanderCurveCount (fun i => (Q i).boundary ℝ) = a ∧
      q ∈ s ∧ q ∈ closure ((T ∩ {x | A x = 0}) \ {q}) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ β' : ℝ, β' ∈ Ioo 0 ε ∧ ∃ γ' : ℝ, γ' ∈ Ioo 0 ε ∧
          Nonempty (AlexanderCollarSlab T A q β') ∧
          Nonempty (AlexanderCollarSlab T (-A) q γ') := by
  have hsub : T ∩ {x | A x = 0} ⊆ S ∩ {x | A x = 0} :=
    fun x hx => ⟨hs (hsection hx).1, (hsection hx).2⟩
  obtain ⟨m, N, Q, hm, hQ, hQfull, hQpair, hbranch, hcount, hq, hacc⟩ :=
    hchild.exists_branching_family_at_common_point ha hsub n P hP
      (r := ∅) (empty_subset _) (by simpa only [empty_union] using hfull) hpair
  have hqs : q ∈ s := (hsection hq).1
  obtain ⟨⟨M⟩, ⟨Mneg⟩⟩ := hcollars hqs
  refine ⟨m, N, Q, hm, hQ, hQfull, hQpair, hbranch, hcount, hqs, hacc, ?_⟩
  intro ε hε
  let β' := min β ε / 2
  let γ' := min γ ε / 2
  have hβmin : 0 < min β ε := lt_min M.width_pos hε
  have hγmin : 0 < min γ ε := lt_min Mneg.width_pos hε
  have hβ' : β' ∈ Ioo 0 ε :=
    ⟨half_pos hβmin, (half_lt_self hβmin).trans_le (min_le_right _ _)⟩
  have hγ' : γ' ∈ Ioo 0 ε :=
    ⟨half_pos hγmin, (half_lt_self hγmin).trans_le (min_le_right _ _)⟩
  have hβ'β : β' ≤ β := (half_lt_self hβmin).le.trans (min_le_left _ _)
  have hγ'γ : γ' ≤ γ := (half_lt_self hγmin).le.trans (min_le_left _ _)
  obtain ⟨M', _, _, _⟩ := M.exists_width_restriction hβ'.1 hβ'β
  obtain ⟨Mneg', _, _, _⟩ := Mneg.exists_width_restriction hγ'.1 hγ'γ
  exact ⟨β', hβ', γ', hγ', ⟨M'⟩, ⟨Mneg'⟩⟩

end Geometry
