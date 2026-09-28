import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBranchingCollars
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderDistantBranchingCollars
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderSelectedBranchingCollars











set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem HasBranchingCollars.of_supported_capped_cut
    {W : AlexanderSectionProfile E} (hW : W.HasBranchingCollars)
    (L : AlexanderSectionProfile E) {s s' d : Set E} (H : E ≃ₜ E)
    (hL : L.carrier = H '' (s ∪ d)) (hLA : L.height = W.height)
    (hsupport : Function.support L.charge ⊆ Function.support W.charge)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = W.carrier)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKs : K.space = s)
    (hcut : s ∩ s' ⊆ {x | W.height x = 0}) (hd : d ⊆ {x | W.height x = 0})
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ c, W.charge c ≠ 0 → c ≠ 0 → δ < |c|)
    (hfix : ∀ x, δ ≤ |W.height x| → H x = x)
    {m : ℕ} (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)) {q : E}
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hfull : W.carrier ∩ {x | W.height x = 0} = ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    (hselected : (H '' (s ∪ d)) ∩ {x | W.height x = 0} ⊆
      s ∩ {x | W.height x = 0})
    {β γ : ℝ} (hcollars : q ∈ s →
      Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) W.height q β) ∧
      Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-W.height) q γ)) :
    L.HasBranchingCollars := by
  intro c hc
  have hchild : HasAlexanderCurvePresentation
      ((H '' (s ∪ d)) ∩ {x | W.height x = c}) (L.charge c) := by
    simpa only [hL, hLA] using L.presentation c
  by_cases hc0 : c = 0
  · subst c
    obtain ⟨k, N, Q, hk, hQ, hQfull, hQpair, hbranch, hcount, _, hacc, hsmall⟩ :=
      Geometry.exists_selected_child_branching_collars
        (subset_union_left.trans hunion.subset) hselected hcollars
        n P hP hfull hpair hchild hc
    refine ⟨k, N, Q, q, hk, hQ, ?_, hQpair, hbranch, hcount, ?_, ?_⟩
    · simpa only [hL, hLA] using hQfull
    · simpa only [hL, hLA] using hacc
    · intro ε hε
      have hzero : W.height - AffineMap.const ℝ E 0 = W.height := by
        ext x
        change W.height x - 0 = W.height x
        exact sub_zero _
      simpa only [hL, hLA, hzero] using hsmall ε hε
  · have hcW : W.charge c ≠ 0 := hsupport hc
    obtain ⟨k, N, Q, p, _, hQ, hQfull, hQpair, _, _, _, hsmall⟩ := hW c hcW
    obtain ⟨β', _, γ', _, ⟨M⟩, ⟨Mneg⟩⟩ := hsmall 1 zero_lt_one
    obtain ⟨_, l, N', Q', hl, hQ', hQ'full, hQ'pair, hbranch, hcount,
        _, hacc, hcollars'⟩ :=
      M.exists_distant_child_branching_collars Mneg hs hs' hunion K hK hKs hcut hd
        N Q hQ hQfull hQpair hδ (hgap c hcW hc0) H hfix hchild hc
    refine ⟨l, N', Q', p, hl, hQ', ?_, hQ'pair, hbranch, hcount, ?_, ?_⟩
    · simpa only [hL, hLA] using hQ'full
    · simpa only [hL, hLA] using hacc
    · intro ε hε
      obtain ⟨β'', hβ'', γ'', hγ'', _, _, hpos, hneg⟩ := hcollars' ε hε
      simpa only [hL, hLA] using
        (show ∃ b : ℝ, b ∈ Ioo 0 ε ∧ ∃ g : ℝ, g ∈ Ioo 0 ε ∧
          Nonempty (AlexanderCollarSlab (H '' (s ∪ d))
            (W.height - AffineMap.const ℝ E c) p b) ∧
          Nonempty (AlexanderCollarSlab (H '' (s ∪ d))
            (-(W.height - AffineMap.const ℝ E c)) p g) from
          ⟨β'', hβ'', γ'', hγ'', hpos, hneg⟩)

end Geometry.AlexanderSectionProfile
