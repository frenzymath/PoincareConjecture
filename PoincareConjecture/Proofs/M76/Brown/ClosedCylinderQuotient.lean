import PoincareConjecture.Proofs.M76.Brown.BicollarEndGeometry
import PoincareConjecture.Proofs.M76.Brown.CompactifiedPolarFibers
import Mathlib.Topology.Constructions.SumProd











set_option autoImplicit false

open Set Metric Topology
open scoped OnePoint

namespace BrownSchoenflies

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]




theorem exists_closed_cylinder_quotient [Nonempty (sphere (0 : E) 1)]
    (e : OpenPartialHomeomorph (sphere (0 : E) 1 × Ioo (-1 : ℝ) 1) X)
    (hes : e.source = univ) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hdis : Disjoint A B)
    (hcover : A ∪ range (closedBicollarMap e hes) ∪ B = univ)
    (hAend : ∀ z, closedBicollarMap e hes z ∈ A ↔ (z.2 : ℝ) = -1)
    (hBend : ∀ z, closedBicollarMap e hes z ∈ B ↔ (z.2 : ℝ) = 1) :
    ∃ q : C(X, OnePoint E), Function.Surjective q ∧
      (∀ x ∈ A, q x = ((0 : E) : OnePoint E)) ∧
      (∀ x ∈ B, q x = ∞) ∧
      ∀ z, q (closedBicollarMap e hes z) = compactifiedPolar z := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let : CompactSpace (sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  let Z := A ⊕ ((sphere (0 : E) 1 × Icc (-1 : ℝ) 1) ⊕ B)
  let F : C(Z, X) :=
    ⟨Sum.elim Subtype.val (Sum.elim (closedBicollarMap e hes) Subtype.val),
      continuous_subtype_val.sumElim
        ((closedBicollarMap e hes).continuous.sumElim continuous_subtype_val)⟩
  let L : C(Z, OnePoint E) :=
    ⟨Sum.elim (fun _ => ((0 : E) : OnePoint E))
        (Sum.elim compactifiedPolar (fun _ => ∞)),
      continuous_const.sumElim (continuous_compactifiedPolar.sumElim continuous_const)⟩
  have hF : Function.Surjective F := by
    intro x
    have hx : x ∈ A ∪ range (closedBicollarMap e hes) ∪ B :=
      hcover.symm.subset (mem_univ x)
    rcases hx with (hx | ⟨z, rfl⟩) | hx
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr (Sum.inl z), rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨x, hx⟩), rfl⟩
  have hfactor : Function.FactorsThrough L F := by
    intro x y hxy
    rcases x with a | (z | b) <;> rcases y with a' | (w | b')
    · rfl
    · change (a : X) = closedBicollarMap e hes w at hxy
      change ((0 : E) : OnePoint E) = compactifiedPolar w
      apply ((compactifiedPolar_eq_zero_iff w).mpr ((hAend w).mp ?_)).symm
      rw [← hxy]
      exact a.property
    · change (a : X) = (b' : X) at hxy
      have hb : (a : X) ∈ B := by rw [hxy]; exact b'.property
      exact False.elim (Set.disjoint_left.mp hdis a.property hb)
    · change closedBicollarMap e hes z = (a' : X) at hxy
      change compactifiedPolar z = ((0 : E) : OnePoint E)
      apply (compactifiedPolar_eq_zero_iff z).mpr ((hAend z).mp ?_)
      rw [hxy]
      exact a'.property
    · change closedBicollarMap e hes z = closedBicollarMap e hes w at hxy
      exact congrArg compactifiedPolar (closedBicollarMap_injective e hes hxy)
    · change closedBicollarMap e hes z = (b' : X) at hxy
      change compactifiedPolar z = ∞
      apply (compactifiedPolar_eq_infty_iff z).mpr ((hBend z).mp ?_)
      rw [hxy]
      exact b'.property
    · change (b : X) = (a' : X) at hxy
      have ha : (b : X) ∈ A := by rw [hxy]; exact a'.property
      exact False.elim (Set.disjoint_left.mp hdis ha b.property)
    · change (b : X) = closedBicollarMap e hes w at hxy
      change ∞ = compactifiedPolar w
      apply ((compactifiedPolar_eq_infty_iff w).mpr ((hBend w).mp ?_)).symm
      rw [← hxy]
      exact b.property
    · rfl
  have hquot := F.continuous.isClosedMap.isQuotientMap F.continuous hF
  let q : C(X, OnePoint E) := hquot.lift L hfactor
  have hqF (z : Z) : q (F z) = L z :=
    congrArg (fun g : C(Z, OnePoint E) => g z) (hquot.lift_comp L hfactor)
  have hqC (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
      q (closedBicollarMap e hes z) = compactifiedPolar z := hqF (Sum.inr (Sum.inl z))
  refine ⟨q, ?_, ?_, ?_, hqC⟩
  · intro y
    obtain ⟨z, hz⟩ := compactifiedPolar_surjective y
    exact ⟨closedBicollarMap e hes z, (hqC z).trans hz⟩
  · intro x hx
    exact hqF (Sum.inl ⟨x, hx⟩)
  · intro x hx
    exact hqF (Sum.inr (Sum.inr ⟨x, hx⟩))

end BrownSchoenflies
