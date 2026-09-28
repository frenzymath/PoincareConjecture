import PoincareConjecture.Proofs.M11.SpatialCalculus
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace TopologicalSpace.Opens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mfderiv_curve_eq_deriv_val (U : Opens E) {f : ℝ → U} {s : ℝ}
    (hf : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f s) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f s (1 : ℝ) = deriv (fun t => (f t).val) s := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (Subtype.val : U → E) (f s) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hd := mfderiv_comp_apply s hi hf (1 : ℝ)
  rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val, mfderiv_eq_fderiv] at hd
  change fderiv ℝ (fun t => (f t).val) s (1 : ℝ) =
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f s (1 : ℝ) at hd
  exact hd.symm

theorem mfderivWithin_curve_eq_derivWithin_val (U : Opens E)
    {f : ℝ → U} {J : Set ℝ} {s : ℝ}
    (hf : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f J s)
    (hJ : UniqueDiffWithinAt ℝ J s) :
    mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f J s (1 : ℝ) =
      derivWithin (fun t => (f t).val) J s := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (Subtype.val : U → E) (f s) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hd := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp_mfderivWithin s hi hf hJ.uniqueMDiffWithinAt)
  rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val, mfderivWithin_eq_fderivWithin] at hd
  change fderivWithin ℝ (fun t => (f t).val) J s (1 : ℝ) =
    mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f J s (1 : ℝ) at hd
  exact hd.symm

end TopologicalSpace.Opens
