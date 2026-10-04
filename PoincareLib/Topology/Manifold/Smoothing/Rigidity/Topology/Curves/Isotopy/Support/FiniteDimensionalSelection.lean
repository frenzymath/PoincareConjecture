import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Support.RelativePLPasting
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous finite PL selections with finite-dimensional targets

A finite continuous linear coordinate equivalence transports the existing
real-coordinate selection and pasting constructions to the original target.
No new subdivision or affine-selection argument is needed.
-/

set_option autoImplicit false
open Set

namespace Geometry

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Continuous selection between two finite PL maps retains finite PL
regularity for any finite-dimensional real normed target. -/
theorem FinitePiecewiseAffineOn.continuous_selection_finiteDimensional
    {f₀ f₁ g : E → F} {C : Set E} (h₀ : FinitePiecewiseAffineOn f₀ C)
    (h₁ : FinitePiecewiseAffineOn f₁ C) (hg : ContinuousOn g C)
    (hselect : ∀ x ∈ C, g x = f₀ x ∨ g x = f₁ x) :
    FinitePiecewiseAffineOn g C := by
  let e := (Module.finBasis ℝ F).equivFunL
  have hcoords : FinitePiecewiseAffineOn (e ∘ g) C :=
    (h₀.postcomp e.toContinuousLinearMap.toContinuousAffineMap).continuous_selection_pi
      (h₁.postcomp e.toContinuousLinearMap.toContinuousAffineMap)
      (e.continuous.comp_continuousOn hg)
      (fun x hx => (hselect x hx).imp (congrArg e) (congrArg e))
  exact (hcoords.postcomp e.symm.toContinuousLinearMap.toContinuousAffineMap).congr
    (fun x _ => e.symm_apply_apply (g x))

/-- Closed-support pasting inside a finite carrier works in the original
finite-dimensional target, including when the support has empty interior. -/
theorem FinitePiecewiseAffineOn.closed_paste_on_carrier_finiteDimensional
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsClosed C)
    {old f g : E → F}
    (hold : FinitePiecewiseAffineOn old K.space)
    (hf : FinitePiecewiseAffineOn f C) (hg : ContinuousOn g K.space)
    (hgin : EqOn g f (K.space ∩ C))
    (hgout : EqOn g old (K.space \ C)) :
    FinitePiecewiseAffineOn g K.space := by
  let e := (Module.finBasis ℝ F).equivFunL
  have hcoords : FinitePiecewiseAffineOn (e ∘ g) K.space :=
    FinitePiecewiseAffineOn.closed_paste_on_carrier K hK hC
      (hold.postcomp e.toContinuousLinearMap.toContinuousAffineMap)
      (hf.postcomp e.toContinuousLinearMap.toContinuousAffineMap)
      (e.continuous.comp_continuousOn hg)
      (fun x hx => congrArg e (hgin hx))
      (fun x hx => congrArg e (hgout hx))
  exact (hcoords.postcomp e.symm.toContinuousLinearMap.toContinuousAffineMap).congr
    (fun x _ => e.symm_apply_apply (g x))

end Geometry
