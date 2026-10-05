import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.Realization
import PoincareLib.Geometry.Spacetime.Realization.Box.Spatial.Calculus
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Actual velocity in an open Euclidean subset

The coordinate calculation in Morgan-Tian Definitions 6.1-6.2,
pp. 105-106, uses the actual derivative of the spatial inclusion.
M11 identifies that inclusion differential with the identity.
-/

set_option autoImplicit false
-- Both tangent fibers retain the same ambient vector-space model.
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace TopologicalSpace.Opens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A differentiable curve in an open subset has the ambient inclusion
velocity, the coordinate identity in Definitions 6.1-6.2, pp. 105-106. -/
theorem mfderiv_curve_eq_deriv_val (U : Opens E) {f : ℝ → U} {s : ℝ}
    (hf : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f s) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f s (1 : ℝ) = deriv (fun t => (f t).val) s := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (Subtype.val : U → E) (f s) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hd := mfderiv_comp_apply s hi hf (1 : ℝ)
  rw [PoincareMT.Proofs.M11.mfderiv_openSubtype_val, mfderiv_eq_fderiv] at hd
  change fderiv ℝ (fun t => (f t).val) s (1 : ℝ) =
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f s (1 : ℝ) at hd
  exact hd.symm

/-- The same actual inclusion velocity identity holds for unique
within derivatives, including closed endpoints in Lemma 6.8,
pp. 108-109. -/
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
  rw [PoincareMT.Proofs.M11.mfderiv_openSubtype_val, mfderivWithin_eq_fderivWithin] at hd
  change fderivWithin ℝ (fun t => (f t).val) J s (1 : ℝ) =
    mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) f J s (1 : ℝ) at hd
  exact hd.symm

end TopologicalSpace.Opens
