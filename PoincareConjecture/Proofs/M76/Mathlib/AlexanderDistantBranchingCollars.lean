import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBranchingPoint
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderDistantCollarRestriction

set_option autoImplicit false

open Set

namespace Geometry.AlexanderCollarSlab

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

theorem exists_distant_child_branching_collars
    {S s₀ s₁ d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {c β γ : ℝ}
    (M : AlexanderCollarSlab S (A - AffineMap.const ℝ E c) q β)
    (Mneg : AlexanderCollarSlab S (-(A - AffineMap.const ℝ E c)) q γ)
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (hunion : s₀ ∪ s₁ = S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKs : K.space = s₀)
    (hcut : s₀ ∩ s₁ ⊆ {x | A x = 0}) (hd : d ⊆ {x | A x = 0})
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hfull : S ∩ {x | A x = c} = ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    {δ : ℝ} (hδ : 0 < δ) (hc : δ < |c|)
    (H : E ≃ₜ E) (hfix : ∀ x, δ ≤ |A x| → H x = x)
    {a : ℕ} (hchild : HasAlexanderCurvePresentation
      ((H '' (s₀ ∪ d)) ∩ {x | A x = c}) a) (ha : a ≠ 0) :
    (H '' (s₀ ∪ d)) ∩ {x | A x = c} = s₀ ∩ {x | A x = c} ∧
      ∃ (m : ℕ) (N : Fin m → ℕ) (Q : ∀ i, Polygon E (N i + 3)),
        0 < m ∧
        (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges) ∧
        (H '' (s₀ ∪ d)) ∩ {x | A x = c} = ⋃ i, (Q i).boundary ℝ ∧
        Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ {q}) ∧
        (¬ Pairwise (fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ))) ∧
        alexanderCurveCount (fun i => (Q i).boundary ℝ) = a ∧
        q ∈ s₀ ∧ q ∈ closure (((H '' (s₀ ∪ d)) ∩ {x | A x = c}) \ {q}) ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ β' : ℝ, β' ∈ Ioo 0 ε ∧ ∃ γ' : ℝ, γ' ∈ Ioo 0 ε ∧
            ((H '' (s₀ ∪ d)) ∩ {x | (A - AffineMap.const ℝ E c) x ∈ Icc 0 β'} =
              s₀ ∩ {x | (A - AffineMap.const ℝ E c) x ∈ Icc 0 β'}) ∧
            ((H '' (s₀ ∪ d)) ∩ {x | (-(A - AffineMap.const ℝ E c)) x ∈ Icc 0 γ'} =
              s₀ ∩ {x | (-(A - AffineMap.const ℝ E c)) x ∈ Icc 0 γ'}) ∧
            Nonempty (AlexanderCollarSlab (H '' (s₀ ∪ d))
              (A - AffineMap.const ℝ E c) q β') ∧
            Nonempty (AlexanderCollarSlab (H '' (s₀ ∪ d))
              (-(A - AffineMap.const ℝ E c)) q γ') := by
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hc
    exact (not_lt_of_ge hδ.le) hc
  have hdlevel : Disjoint d {x | A x = c} := by
    apply disjoint_left.mpr
    intro x hxd hx
    exact hc0 (hx.symm.trans (hd hxd))
  have hlevel := H.capped_image_inter_eq_of_fixedOn (s := s₀)
    (V := {x | A x = c}) (fun x hx => hfix x (by
      change A x = c at hx
      rw [hx]
      exact hc.le)) hdlevel
  have hsS : s₀ ⊆ S := subset_union_left.trans hunion.subset
  have hsub : (H '' (s₀ ∪ d)) ∩ {x | A x = c} ⊆ S ∩ {x | A x = c} :=
    fun x hx => ⟨hsS (hlevel.subset hx).1, (hlevel.subset hx).2⟩
  obtain ⟨m, N, Q, hm, hQ, hQfull, hQpair, hbranch, hcount, hq, hacc⟩ :=
    hchild.exists_branching_family_at_common_point ha hsub n P hP
      (r := ∅) (empty_subset _) (by simpa only [empty_union] using hfull) hpair
  have hqs : q ∈ s₀ := (hlevel.subset hq).1
  refine ⟨hlevel, m, N, Q, hm, hQ, hQfull, hQpair, hbranch, hcount, hqs, hacc, ?_⟩
  intro ε hε
  obtain ⟨β', hβ', _, hpositive⟩ := M.exists_small_supported_capped_cut
    hs₀ hs₁ hunion hqs K hK hKs A hδ hc (fun _ => rfl) hcut hd hε
  have hnegdist (x : E) : |(-(A - AffineMap.const ℝ E c)) x| = |A x - c| := by
    change |-(A x - c)| = |A x - c|
    exact abs_neg _
  obtain ⟨γ', hγ', _, hnegative⟩ := Mneg.exists_small_supported_capped_cut
    hs₀ hs₁ hunion hqs K hK hKs A hδ hc hnegdist hcut hd hε
  obtain ⟨hposlevel, hpos⟩ := hpositive H hfix
  obtain ⟨hneglevel, hneg⟩ := hnegative H hfix
  exact ⟨β', hβ', γ', hγ', hposlevel, hneglevel, hpos, hneg⟩

end Geometry.AlexanderCollarSlab
