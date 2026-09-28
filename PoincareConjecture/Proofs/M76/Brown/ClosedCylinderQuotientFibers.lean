import PoincareConjecture.Proofs.M76.Brown.ClosedCylinderQuotient










set_option autoImplicit false

open Set Metric
open scoped OnePoint

namespace BrownSchoenflies

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]




theorem closed_cylinder_quotient_fibers
    (e : OpenPartialHomeomorph (sphere (0 : E) 1 × Ioo (-1 : ℝ) 1) X)
    (hes : e.source = univ) {A B : Set X}
    (hcover : A ∪ range (closedBicollarMap e hes) ∪ B = univ)
    (hAend : ∀ z, closedBicollarMap e hes z ∈ A ↔ (z.2 : ℝ) = -1)
    (hBend : ∀ z, closedBicollarMap e hes z ∈ B ↔ (z.2 : ℝ) = 1)
    (q : X → OnePoint E)
    (hqA : ∀ x ∈ A, q x = ((0 : E) : OnePoint E))
    (hqB : ∀ x ∈ B, q x = ∞)
    (hqC : ∀ z, q (closedBicollarMap e hes z) = compactifiedPolar z) :
    (∀ x, q x = ((0 : E) : OnePoint E) ↔ x ∈ A) ∧
      (∀ x, q x = ∞ ↔ x ∈ B) ∧
      ∀ x y, q x = q y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B) := by
  have hzero (x : X) : q x = ((0 : E) : OnePoint E) ↔ x ∈ A := by
    constructor
    · intro hx
      have hxc : x ∈ A ∪ range (closedBicollarMap e hes) ∪ B :=
        hcover.symm.subset (mem_univ x)
      rcases hxc with (hxA | ⟨z, rfl⟩) | hxB
      · exact hxA
      · exact (hAend z).mpr ((compactifiedPolar_eq_zero_iff z).mp ((hqC z).symm.trans hx))
      · exact False.elim (OnePoint.infty_ne_coe (0 : E) ((hqB x hxB).symm.trans hx))
    · exact hqA x
  have hinfty (x : X) : q x = ∞ ↔ x ∈ B := by
    constructor
    · intro hx
      have hxc : x ∈ A ∪ range (closedBicollarMap e hes) ∪ B :=
        hcover.symm.subset (mem_univ x)
      rcases hxc with (hxA | ⟨z, rfl⟩) | hxB
      · exact False.elim (OnePoint.coe_ne_infty (0 : E) ((hqA x hxA).symm.trans hx))
      · exact (hBend z).mpr ((compactifiedPolar_eq_infty_iff z).mp ((hqC z).symm.trans hx))
      · exact hxB
    · exact hqB x
  refine ⟨hzero, hinfty, ?_⟩
  intro x y
  constructor
  · intro hxy
    by_cases hxA : x ∈ A
    · exact Or.inr (Or.inl ⟨hxA, (hzero y).mp (hxy.symm.trans (hqA x hxA))⟩)
    by_cases hxB : x ∈ B
    · exact Or.inr (Or.inr ⟨hxB, (hinfty y).mp (hxy.symm.trans (hqB x hxB))⟩)
    have hyA : y ∉ A := fun hy => hxA ((hzero x).mp (hxy.trans (hqA y hy)))
    have hyB : y ∉ B := fun hy => hxB ((hinfty x).mp (hxy.trans (hqB y hy)))
    have hxC : x ∈ range (closedBicollarMap e hes) :=
      ((hcover.symm.subset (mem_univ x)).resolve_right hxB).resolve_left hxA
    have hyC : y ∈ range (closedBicollarMap e hes) :=
      ((hcover.symm.subset (mem_univ y)).resolve_right hyB).resolve_left hyA
    obtain ⟨z, rfl⟩ := hxC
    obtain ⟨w, rfl⟩ := hyC
    have hpolar : compactifiedPolar z = compactifiedPolar w :=
      (hqC z).symm.trans (hxy.trans (hqC w))
    rcases (compactifiedPolar_fibers z w).mp hpolar with hzw | ⟨hz, hw⟩ | ⟨hz, hw⟩
    · exact Or.inl (congrArg (closedBicollarMap e hes) hzw)
    · exact Or.inr (Or.inl ⟨(hAend z).mpr hz, (hAend w).mpr hw⟩)
    · exact Or.inr (Or.inr ⟨(hBend z).mpr hz, (hBend w).mpr hw⟩)
  · rintro (rfl | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · rfl
    · exact (hqA x hx).trans (hqA y hy).symm
    · exact (hqB x hx).trans (hqB y hy).symm

end BrownSchoenflies
