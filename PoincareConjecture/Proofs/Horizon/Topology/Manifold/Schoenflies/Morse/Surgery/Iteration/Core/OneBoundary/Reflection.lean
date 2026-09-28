import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Caps
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift.Reflection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}

def reflected (D : SphereSurgeryCoreCap v g B) :
    SphereSurgeryCoreCap v (fun p => heightReflection D.unit_v (g p)) ∅ where
  chart := D.chart
  source := D.source
  smooth := D.smooth
  symm_smooth := D.symm_smooth
  unit_v := D.unit_v
  center := -D.center
  scale := -D.scale
  scale_ne_zero := neg_ne_zero.mpr D.scale_ne_zero
  planeMap := D.planeMap
  parametrization := fun x => heightReflection D.unit_v (D.parametrization x)
  parametrization_smooth := by
    have h := (heightReflection D.unit_v).contMDiff.comp D.parametrization_smooth.contMDiff
    exact contMDiff_iff_contDiff.mp h
  parametrization_injective := (heightReflection D.unit_v).injective.comp D.parametrization_injective
  parametrization_deriv_injective := by
    intro x
    let R := heightReflection D.unit_v
    have hchain := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3) x
      (R.contMDiff.mdifferentiable (by simp) _)
      (D.parametrization_smooth.contMDiff.mdifferentiable (by simp) x)
    have hinj := (R.mfderivToContinuousLinearEquiv (by simp) (D.parametrization x)).injective.comp
      (show Injective (mfderiv (𝓡 2) (𝓡 3) D.parametrization x) by
        rw [mfderiv_eq_fderiv]
        exact D.parametrization_deriv_injective x)
    change Injective ((mfderiv (𝓡 3) (𝓡 3) R (D.parametrization x)).comp
      (mfderiv (𝓡 2) (𝓡 3) D.parametrization x)) at hinj
    rw [← hchain] at hinj
    rw [mfderiv_eq_fderiv] at hinj
    exact hinj
  parametrization_eq := fun x hx => congrArg (heightReflection D.unit_v) (D.parametrization_eq x hx)
  boundary_height := by
    intro x hx
    rw [inner_heightReflection, D.boundary_height x hx]
  range_eq := by
    change (heightReflection D.unit_v ∘ D.parametrization) '' closedBall (0 : E2) 1 = _
    rw [image_comp, D.range_eq]
    exact image_heightReflection_liftPlaneDiffeomorph D.unit_v D.center D.scale
      D.scale_ne_zero D.planeMap _
  avoids_protected := by simp

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
