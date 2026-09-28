import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityPresentation
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBranchingSection

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem HasAlexanderCurvePresentation.exists_branching_family
    {S : Set E} {a : ℕ} (h : HasAlexanderCurvePresentation S a) (ha : a ≠ 0) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)) (q : E),
      0 < m ∧
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      S = ⋃ i, (P i).boundary ℝ ∧
      Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}) ∧
      (¬ Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))) ∧
      alexanderCurveCount (fun i => (P i).boundary ℝ) = a ∧
      q ∈ S ∧ q ∈ closure (S \ {q}) := by
  classical
  obtain ⟨m, n, P, r, hP, hr, hcover, hpair, hcount⟩ := h
  have hbranch : ¬ Pairwise (fun i j =>
      Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) := by
    intro hd
    exact ha (hcount.symm.trans ((alexanderCurveCount_eq_zero_iff _).mpr hd))
  have hmeet := hbranch
  change ¬ ∀ i j, i ≠ j → Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ) at hmeet
  push Not at hmeet
  obtain ⟨i, j, hij, hmeet⟩ := hmeet
  obtain ⟨q, hqi, hqj⟩ := not_disjoint_iff.mp hmeet
  have hrq : r = {q} := hr.eq_singleton_of_mem (hpair hij ⟨hqi, hqj⟩)
  have hqunion : q ∈ ⋃ k, (P k).boundary ℝ := mem_iUnion.mpr ⟨i, hqi⟩
  have hfull : S = ⋃ k, (P k).boundary ℝ := by
    rw [hcover, hrq, union_eq_self_of_subset_left (singleton_subset_iff.mpr hqunion)]
  have hpairq : Pairwise (fun i j =>
      (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}) := hrq ▸ hpair
  refine ⟨m, n, P, q, lt_of_le_of_lt (Nat.zero_le i.val) i.isLt,
    hP, hfull, hpairq, hbranch, hcount, hfull.symm ▸ hqunion, ?_⟩
  exact Polygon.mem_closure_punctured_section_of_branching n P hP q hpairq hbranch
    (fun k x hx => hfull.symm ▸ mem_iUnion.mpr ⟨k, hx⟩)

end Set
