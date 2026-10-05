import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.IntrinsicBranchingSection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderComplexitySum

/-!
# Binary Alexander induction on complete section profiles

The measure is the finite total of actual section charges, not the
vertices of an image triangulation. Binary induction retains both literal
child surfaces and uses their explicit reconstruction implication. Equal
heights of subdivision vertices are unrestricted. See Alexander 1924,
pp. 6--8 and M76 derivation 269.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complete geometric charge profile of one literal surface and
affine height. No genericity condition on a triangulation is required.
See Alexander pp. 6--8 and M76 derivation 269. -/
structure AlexanderSectionProfile where
  /-- The literal embedded carrier. -/
  carrier : Set E
  /-- The actual affine height used by every section. -/
  height : E →ᵃ[ℝ] ℝ
  /-- The natural Alexander charge of every real-height section. -/
  charge : ℝ → ℕ
  /-- Complete polygon and residue witnesses for every section charge. -/
  presentation : ∀ c,
    HasAlexanderCurvePresentation (carrier ∩ {x | height x = c}) (charge c)
  /-- Only finitely many real heights have positive charge. -/
  finite_support : (Function.support charge).Finite

variable {E}

namespace AlexanderSectionProfile

/-- The discrete induction measure sums the actual charge over its own
finite support. Empty support has complexity zero. See Alexander p. 7
and M76 derivation 269. -/
noncomputable def complexity (P : AlexanderSectionProfile E) : ℕ :=
  ∑ c ∈ P.finite_support.toFinset, P.charge c

/-- Each actual section charge is bounded by the complete finite total.
See Alexander pp. 6--7 and M76 derivation 269. -/
theorem charge_le_complexity (P : AlexanderSectionProfile E) (c : ℝ) :
    P.charge c ≤ P.complexity := by
  classical
  by_cases hc : P.charge c = 0
  · rw [hc]
    exact Nat.zero_le _
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (P.finite_support.mem_toFinset.mpr hc)

/-- Zero total is exactly vanishing of every actual section charge. This
does not assert regular local geometry. See Alexander pp. 6--7 and
M76 derivation 269. -/
theorem complexity_eq_zero_iff (P : AlexanderSectionProfile E) :
    P.complexity = 0 ↔ ∀ c, P.charge c = 0 := by
  classical
  constructor
  · intro h c
    exact Nat.eq_zero_of_le_zero (h ▸ P.charge_le_complexity c)
  · intro h
    simp only [complexity, h, Finset.sum_const_zero]

/-- A nonzero finite total selects a genuine nonzero-charge height,
independently of the vertex heights of any triangulation.
See Alexander p. 7 and M76 derivation 269. -/
theorem exists_nonzero_charge (P : AlexanderSectionProfile E)
    (hP : P.complexity ≠ 0) : ∃ c : ℝ, P.charge c ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact hP (P.complexity_eq_zero_iff.mpr h)

variable [FiniteDimensional ℝ E]

/-- A nonzero total supplies the complete actual branching section,
including its common point and nonisolation. Equal-height image vertices
play no role in this selection. See Alexander pp. 6--7 and derivation 269. -/
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
/-- Two admissible actual child profiles with a strict combined charge
decrease and a reconstruction implication reduce the geometric goal to its
zero-charge case. All geometric admissibility, base and reconstruction
requirements remain explicit; no regularity follows merely from charge
zero. See Alexander pp. 6--8 and M76 derivation 269. -/
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
