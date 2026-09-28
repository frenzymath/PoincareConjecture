import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicBranchingSection
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexitySum











set_option autoImplicit false

open Set

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]




structure AlexanderSectionProfile where

  carrier : Set E

  height : E →ᵃ[ℝ] ℝ

  charge : ℝ → ℕ

  presentation : ∀ c,
    HasAlexanderCurvePresentation (carrier ∩ {x | height x = c}) (charge c)

  finite_support : (Function.support charge).Finite

variable {E}

namespace AlexanderSectionProfile




noncomputable def complexity (P : AlexanderSectionProfile E) : ℕ :=
  ∑ c ∈ P.finite_support.toFinset, P.charge c



theorem charge_le_complexity (P : AlexanderSectionProfile E) (c : ℝ) :
    P.charge c ≤ P.complexity := by
  classical
  by_cases hc : P.charge c = 0
  · rw [hc]
    exact Nat.zero_le _
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (P.finite_support.mem_toFinset.mpr hc)




theorem complexity_eq_zero_iff (P : AlexanderSectionProfile E) :
    P.complexity = 0 ↔ ∀ c, P.charge c = 0 := by
  classical
  constructor
  · intro h c
    exact Nat.eq_zero_of_le_zero (h ▸ P.charge_le_complexity c)
  · intro h
    simp only [complexity, h, Finset.sum_const_zero]




theorem exists_nonzero_charge (P : AlexanderSectionProfile E)
    (hP : P.complexity ≠ 0) : ∃ c : ℝ, P.charge c ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact hP (P.complexity_eq_zero_iff.mpr h)

variable [FiniteDimensional ℝ E]




theorem exists_branching_section (P : AlexanderSectionProfile E)
    (hP : P.complexity ≠ 0) :
    ∃ (c : ℝ) (m : ℕ) (n : Fin m → ℕ)
      (Q : ∀ i, Polygon E (n i + 3)) (q : E),
      P.charge c ≠ 0 ∧ 0 < m ∧
      (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges) ∧
      P.carrier ∩ {x | P.height x = c} = ⋃ i, (Q i).boundary ℝ ∧
      Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ {q}) ∧
      (¬ Pairwise (fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ))) ∧
      alexanderCurveCount (fun i => (Q i).boundary ℝ) = P.charge c ∧
      q ∈ P.carrier ∩ {x | P.height x = c} ∧
      q ∈ closure ((P.carrier ∩ {x | P.height x = c}) \ {q}) := by
  obtain ⟨c, hc⟩ := P.exists_nonzero_charge hP
  obtain ⟨m, n, Q, q, hm, hQ, hcover, hpair, hbranch, hcount, hq, hacc⟩ :=
    (P.presentation c).exists_branching_family hc
  exact ⟨c, m, n, Q, q, hc, hm, hQ, hcover, hpair, hbranch, hcount, hq, hacc⟩

omit [FiniteDimensional ℝ E] in





theorem binary_induction {Admissible : AlexanderSectionProfile E → Prop}
    {Q : Set E → Prop}
    (base : ∀ P, Admissible P → (∀ c, P.charge c = 0) → Q P.carrier)
    (split : ∀ P, Admissible P → ∀ c, P.charge c ≠ 0 →
      ∃ L R : AlexanderSectionProfile E,
        Admissible L ∧ Admissible R ∧
        L.complexity + R.complexity < P.complexity ∧
        (Q L.carrier → Q R.carrier → Q P.carrier))
    (P : AlexanderSectionProfile E) (hP : Admissible P) : Q P.carrier := by
  have hrec : ∀ k : ℕ, ∀ T : AlexanderSectionProfile E,
      T.complexity = k → Admissible T → Q T.carrier := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro T hTk hT
        by_cases hz : T.complexity = 0
        · exact base T hT (T.complexity_eq_zero_iff.mp hz)
        · obtain ⟨c, hc⟩ := T.exists_nonzero_charge hz
          obtain ⟨L, R, hL, hR, hlt, assemble⟩ := split T hT c hc
          have hLlt : L.complexity < k := by omega
          have hRlt : R.complexity < k := by omega
          exact assemble (ih L.complexity hLlt L rfl hL)
            (ih R.complexity hRlt R rfl hR)
  exact hrec P.complexity P rfl hP

end AlexanderSectionProfile

end Geometry
