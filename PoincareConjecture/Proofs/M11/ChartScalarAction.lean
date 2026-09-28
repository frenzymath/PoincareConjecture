import Mathlib.Geometry.Manifold.VectorField.LieBracket





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem extChart_scalar_action (x : M) {y : E} (hy : y ∈ (extChartAt I x).target)
    {f : M → ℝ} (hf : MDifferentiableAt I 𝓘(ℝ) f ((extChartAt I x).symm y))
    (V : ∀ p : M, TangentSpace I p) :
    fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I) y
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) y) =
        mfderiv I 𝓘(ℝ) f ((extChartAt I x).symm y) (V ((extChartAt I x).symm y)) := by
  have hc := mfderiv_comp_mfderivWithin y hf
    (mdifferentiableWithinAt_extChartAt_symm hy)
    (I.uniqueMDiffOn y (extChartAt_target_subset_range x hy))
  rw [mfderivWithin_eq_fderivWithin] at hc
  rw [hc, VectorField.mpullbackWithin_apply]
  change mfderiv I 𝓘(ℝ) f ((extChartAt I x).symm y)
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y).inverse
          (V ((extChartAt I x).symm y)))) = _
  exact congrArg (mfderiv I 𝓘(ℝ) f ((extChartAt I x).symm y))
    ((isInvertible_mfderivWithin_extChartAt_symm hy).self_apply_inverse _)

omit [IsManifold I ∞ M] in
theorem extChart_scalar_derivative (x : M) {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ) f x v =
      fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) v := by
  rw [hf.mfderiv]
  rfl

end PoincareConjecture.Proofs.M11
