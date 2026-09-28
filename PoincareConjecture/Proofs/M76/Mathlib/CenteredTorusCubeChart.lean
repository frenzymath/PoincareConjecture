import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd
import PoincareConjecture.Proofs.M76.Mathlib.CubeShellGeometry










set_option autoImplicit false

open Set Geometry

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]



noncomputable def centeredCubeQuotient :
    OpenPartialHomeomorph CubeShell.Ambient ((AddCircle p × AddCircle p) × AddCircle p) :=
  let A := ContinuousAffineEquiv.constVAdd ℝ CubeShell.Ambient ((p / 2, p / 2), p / 2)
  A.toHomeomorph.toOpenPartialHomeomorph.trans
    (((openPartialHomeomorphCoe p 0).prod (openPartialHomeomorphCoe p 0)).prod
      (openPartialHomeomorphCoe p 0))



theorem centeredCubeQuotient_apply (x : CubeShell.Ambient) :
    centeredCubeQuotient p x =
      ((((p / 2 + x.1.1 : ℝ) : AddCircle p), ((p / 2 + x.1.2 : ℝ) : AddCircle p)),
        ((p / 2 + x.2 : ℝ) : AddCircle p)) := rfl



theorem centeredCubeQuotient_source :
    (centeredCubeQuotient p).source = {x | ‖x‖ < p / 2} := by
  have hcoord (s : ℝ) : p / 2 + s ∈ Ioo 0 (0 + p) ↔ |s| < p / 2 := by
    rw [abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  ext x
  change (x ∈ univ ∧
    ((p / 2 + x.1.1 ∈ Ioo 0 (0 + p) ∧ p / 2 + x.1.2 ∈ Ioo 0 (0 + p)) ∧
      p / 2 + x.2 ∈ Ioo 0 (0 + p))) ↔ ‖x‖ < p / 2
  simp only [mem_univ, true_and, hcoord, Prod.norm_def, Real.norm_eq_abs, max_lt_iff]



theorem centeredCubeQuotient_target :
    (centeredCubeQuotient p).target =
      {z | (z.1.1 ≠ 0 ∧ z.1.2 ≠ 0) ∧ z.2 ≠ 0} := by
  ext z
  change ((((z.1.1 ≠ ((0 : ℝ) : AddCircle p)) ∧
    (z.1.2 ≠ ((0 : ℝ) : AddCircle p))) ∧ (z.2 ≠ ((0 : ℝ) : AddCircle p))) ∧ True) ↔
      ((z.1.1 ≠ 0 ∧ z.1.2 ≠ 0) ∧ z.2 ≠ 0)
  simp




theorem centeredCubeQuotient_transition_mem_piecewiseAffineGroupoid (a b c : ℝ) :
    (((openPartialHomeomorphCoe p a).prod (openPartialHomeomorphCoe p b)).prod
      (openPartialHomeomorphCoe p c)).trans (centeredCubeQuotient p).symm ∈
        piecewiseAffineGroupoid CubeShell.Ambient := by
  let A := ContinuousAffineEquiv.constVAdd ℝ CubeShell.Ambient ((p / 2, p / 2), p / 2)
  have hA : A.symm.toHomeomorph.toOpenPartialHomeomorph ∈
      piecewiseAffineGroupoid CubeShell.Ambient :=
    ⟨locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ,
      locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ⟩
  change (((openPartialHomeomorphCoe p a).prod (openPartialHomeomorphCoe p b)).prod
    (openPartialHomeomorphCoe p c)).trans
    ((((openPartialHomeomorphCoe p 0).prod (openPartialHomeomorphCoe p 0)).prod
      (openPartialHomeomorphCoe p 0)).symm.trans
        A.symm.toHomeomorph.toOpenPartialHomeomorph) ∈ _
  rw [← OpenPartialHomeomorph.trans_assoc]
  simp only [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans]
  exact (piecewiseAffineGroupoid CubeShell.Ambient).trans
    (piecewiseAffineGroupoid_prod _ _
      (piecewiseAffineGroupoid_prod _ _
        (quotient_chart_transition_mem_piecewiseAffineGroupoid p a 0)
        (quotient_chart_transition_mem_piecewiseAffineGroupoid p b 0))
      (quotient_chart_transition_mem_piecewiseAffineGroupoid p c 0)) hA




theorem locallyPiecewiseAffineOn_comp_centeredCubeQuotient
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ((AddCircle p × AddCircle p) × AddCircle p) → F)
    (U : Set ((AddCircle p × AddCircle p) × AddCircle p))
    (hf : let T := ((openPartialHomeomorphCoe p 0).prod
        (openPartialHomeomorphCoe p 0)).prod (openPartialHomeomorphCoe p 0)
      LocallyPiecewiseAffineOn (f ∘ T) (T.source ∩ T ⁻¹' U)) :
    LocallyPiecewiseAffineOn (f ∘ centeredCubeQuotient p)
      ((centeredCubeQuotient p).source ∩ centeredCubeQuotient p ⁻¹' U) := by
  let A := ContinuousAffineEquiv.constVAdd ℝ CubeShell.Ambient ((p / 2, p / 2), p / 2)
  let T := ((openPartialHomeomorphCoe p 0).prod
    (openPartialHomeomorphCoe p 0)).prod (openPartialHomeomorphCoe p 0)
  have hA : LocallyPiecewiseAffineOn A (univ : Set CubeShell.Ambient) :=
    locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ
  have hcomp := hf.comp hA
  change LocallyPiecewiseAffineOn ((f ∘ T) ∘ A)
    ((univ ∩ A ⁻¹' T.source) ∩ (fun x => T (A x)) ⁻¹' U)
  convert hcomp using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_univ, true_and]
  rfl

end AddCircle
