import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd

set_option autoImplicit false

open Set Geometry

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

noncomputable def centeredSquareQuotient :
    OpenPartialHomeomorph (ℝ × ℝ) (AddCircle p × AddCircle p) :=
  let A := ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (p / 2, p / 2)
  A.toHomeomorph.toOpenPartialHomeomorph.trans
    ((openPartialHomeomorphCoe p 0).prod (openPartialHomeomorphCoe p 0))

theorem centeredSquareQuotient_apply (x : ℝ × ℝ) :
    centeredSquareQuotient p x =
      (((p / 2 + x.1 : ℝ) : AddCircle p), ((p / 2 + x.2 : ℝ) : AddCircle p)) := rfl

theorem centeredSquareQuotient_source :
    (centeredSquareQuotient p).source = {x | ‖x‖ < p / 2} := by
  ext x
  change (x ∈ univ ∧
    (p / 2 + x.1 ∈ Ioo 0 (0 + p) ∧ p / 2 + x.2 ∈ Ioo 0 (0 + p))) ↔ ‖x‖ < p / 2
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff, abs_lt, abs_lt]
  simp only [mem_univ, true_and, mem_Ioo, zero_add]
  constructor
  · rintro ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem centeredSquareQuotient_target :
    (centeredSquareQuotient p).target = {z | z.1 ≠ 0 ∧ z.2 ≠ 0} := by
  ext z
  change (((z.1 ≠ ((0 : ℝ) : AddCircle p)) ∧ (z.2 ≠ ((0 : ℝ) : AddCircle p))) ∧ True) ↔
    (z.1 ≠ 0 ∧ z.2 ≠ 0)
  simp

theorem centeredSquareQuotient_transition_mem_piecewiseAffineGroupoid (a b : ℝ) :
    ((openPartialHomeomorphCoe p a).prod (openPartialHomeomorphCoe p b)).trans
      (centeredSquareQuotient p).symm ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
  let A := ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (p / 2, p / 2)
  have hA : A.symm.toHomeomorph.toOpenPartialHomeomorph ∈
      piecewiseAffineGroupoid (ℝ × ℝ) :=
    ⟨locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ,
      locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ⟩
  change ((openPartialHomeomorphCoe p a).prod (openPartialHomeomorphCoe p b)).trans
    (((openPartialHomeomorphCoe p 0).prod (openPartialHomeomorphCoe p 0)).symm.trans
      A.symm.toHomeomorph.toOpenPartialHomeomorph) ∈ piecewiseAffineGroupoid (ℝ × ℝ)
  rw [← OpenPartialHomeomorph.trans_assoc, OpenPartialHomeomorph.prod_symm,
    OpenPartialHomeomorph.prod_trans]
  exact (piecewiseAffineGroupoid (ℝ × ℝ)).trans
    (piecewiseAffineGroupoid_prod _ _
      (quotient_chart_transition_mem_piecewiseAffineGroupoid p a 0)
      (quotient_chart_transition_mem_piecewiseAffineGroupoid p b 0)) hA

end AddCircle
