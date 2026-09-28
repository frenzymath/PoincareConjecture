import PoincareConjecture.Proofs.M76.Mathlib.PolygonZeroSectionPartition
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityPresentation

set_option autoImplicit false

open Set

namespace Polygon

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

theorem exists_decreasing_pointed_zero_presentations
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (q : E)
    (hpair : Pairwise (fun i k => (P i).boundary ℝ ∩ (P k).boundary ℝ ⊆ {q}))
    (hbranch : ¬ Pairwise (fun i k => Disjoint ((P i).boundary ℝ) ((P k).boundary ℝ)))
    (j : ι) (hqP : q ∈ (P j).boundary ℝ)
    {s s' d Z : Set E} (hs : IsClosed s) (hs' : IsClosed s')
    (hinter : s ∩ s' = (P j).boundary ℝ)
    (hcap : d ∩ (s ∪ s') = (P j).boundary ℝ)
    (hfull : (s ∪ s') ∩ Z = ⋃ i, (P i).boundary ℝ) :
    ∃ a₀ a₁ : ℕ,
      HasAlexanderCurvePresentation ((((s ∪ d) ∩ Z) \ d) ∪ (d ∩ {q})) a₀ ∧
      HasAlexanderCurvePresentation ((((s' ∪ d) ∩ Z) \ d) ∪ (d ∩ {q})) a₁ ∧
      a₀ + a₁ < alexanderCurveCount (fun i => (P i).boundary ℝ) := by
  have hbd : (P j).boundary ℝ ⊆ d := hcap.symm.subset.trans inter_subset_left
  have hsection : (s ∪ s') ∩ Z =
      (P j).boundary ℝ ∪ ⋃ i : {i : ι // i ≠ j}, (P i.val).boundary ℝ := by
    rw [hfull]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hi)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hij⟩, hi⟩)
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨j, hx⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.val, hi⟩
  have hdP (i : {i : ι // i ≠ j}) : d ∩ (P i.val).boundary ℝ ⊆ {q} := by
    intro x hx
    have hxS : x ∈ s ∪ s' :=
      (hfull.symm.subset (mem_iUnion.mpr ⟨i.val, hx.2⟩)).1
    exact hpair i.property.symm ⟨hcap.subset ⟨hx.1, hxS⟩, hx.2⟩
  obtain ⟨I, _, _, hzero, hzero', _⟩ := exists_zero_section_cut_partition
    (fun i : {i : ι // i ≠ j} => n i.val) (fun i => P i.val)
    (fun i => (hP i.val).2) (fun i => (hP i.val).1)
    hs hs' hinter q hqP hbd hsection hdP
  have hpresent (J : Set {i : ι // i ≠ j}) :
      HasAlexanderCurvePresentation ((⋃ i : J, (P i.val.val).boundary ℝ) ∪ {q})
        (alexanderCurveCount (fun i : J => (P i.val.val).boundary ℝ)) := by
    apply hasAlexanderCurvePresentation_of_family
      (fun i : J => n i.val.val) (fun i => P i.val.val)
      (fun i => hP i.val.val) (subsingleton_singleton (a := q))
    · exact union_comm _ _
    · intro i k hik
      exact hpair (fun h => hik (Subtype.ext (Subtype.ext h)))
  refine ⟨_, _, hzero.symm ▸ hpresent I, hzero'.symm ▸ hpresent Iᶜ, ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self _)
    (alexanderCurveCount_partition_after_deletion
      (fun i => (P i).boundary ℝ) hbranch j I).1

end Polygon
