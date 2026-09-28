import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

noncomputable section

namespace Poincare.Manifold.VectorField

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

theorem fderiv_comp_extChartAt_symm {f : M → ℝ} {p : M} {z : E}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I p).symm z))
    (hz : z ∈ (extChartAt I p).target) (w : E) :
    fderiv ℝ (f ∘ (extChartAt I p).symm) z w =
      mfderiv I 𝓘(ℝ, ℝ) f ((extChartAt I p).symm z)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z w) := by
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm z := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := p) hz
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hcomp := mfderiv_comp z hf hsymm
  rw [mfderiv_eq_fderiv] at hcomp
  rw [hcomp]
  rfl

theorem isInvertible_mfderiv_extChartAt_symm {p : M} {z : E}
    (hz : z ∈ (extChartAt I p).target) :
    (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z).IsInvertible := by
  have h := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := p) hz
  rwa [I.range_eq_univ, mfderivWithin_univ] at h

theorem mfderiv_action_eq_fderiv_pullback {h : M → ℝ} {p : M} {z : E}
    (hz : z ∈ (extChartAt I p).target)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h ((extChartAt I p).symm z))
    (Z : Π y : M, TangentSpace I y) :
    fderiv ℝ (h ∘ (extChartAt I p).symm) z
        (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z z) =
      mfderiv I 𝓘(ℝ, ℝ) h ((extChartAt I p).symm z)
        (Z ((extChartAt I p).symm z)) := by
  rw [fderiv_comp_extChartAt_symm hh hz, VectorField.mpullback_apply,
    (isInvertible_mfderiv_extChartAt_symm hz).self_apply_inverse]

end Poincare.Manifold.VectorField
