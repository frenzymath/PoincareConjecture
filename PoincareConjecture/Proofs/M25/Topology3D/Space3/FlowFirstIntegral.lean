import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowAlgebra
import Mathlib.Analysis.Calculus.MeanValue











set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (f : E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)



theorem boundedFlow_mapsTo_set {U : Set E} (hz : ∀ x ∉ U, f x = 0) (t : ℝ) :
    MapsTo (fun x => boundedFlow f hK hL x t) U U := by
  intro x hx
  by_contra hflow
  have heq := boundedFlow_eq_self f hK hL (boundedFlow f hK hL x t)
    (hz _ hflow) (-t)
  rw [boundedFlow_neg] at heq
  apply hflow
  change boundedFlow f hK hL x t ∈ U
  rwa [← heq]



theorem boundedFlow_preserves_firstIntegral {U : Set E} (hz : ∀ x ∉ U, f x = 0)
    (A : E → F) (hA : ∀ x ∈ U, DifferentiableAt ℝ A x)
    (hAf : ∀ x ∈ U, fderiv ℝ A x (f x) = 0) (x : E) (hx : x ∈ U) (t : ℝ) :
    A (boundedFlow f hK hL x t) = A x := by
  have hmem (u : ℝ) : boundedFlow f hK hL x u ∈ U :=
    boundedFlow_mapsTo_set f hK hL hz u hx
  have hd (u : ℝ) : HasDerivAt (fun v => A (boundedFlow f hK hL x v)) 0 u := by
    simpa only [Function.comp_def, hAf _ (hmem u)] using
      (hA _ (hmem u)).hasFDerivAt.comp_hasDerivAt u (boundedFlow_hasDerivAt f hK hL x u)
  simpa only [boundedFlow_zero] using
    is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0




theorem boundedFlow_intertwines_on [CompleteSpace F]
    (g : F → F) {K' L' : ℝ≥0} (hgK : LipschitzWith K' g) (hgL : ∀ y, ‖g y‖ ≤ L')
    {S : Set E} (A : E → F) (hA : ∀ y ∈ S, DifferentiableAt ℝ A y)
    (hAg : ∀ y ∈ S, fderiv ℝ A y (f y) = g (A y)) (x : E)
    (hmem : ∀ t, boundedFlow f hK hL x t ∈ S) (t : ℝ) :
    A (boundedFlow f hK hL x t) = boundedFlow g hgK hgL (A x) t := by
  have hd (u : ℝ) : HasDerivAt (fun v => A (boundedFlow f hK hL x v))
      (g (A (boundedFlow f hK hL x u))) u := by
    simpa only [Function.comp_def, hAg _ (hmem u)] using
      (hA _ (hmem u)).hasFDerivAt.comp_hasDerivAt u (boundedFlow_hasDerivAt f hK hL x u)
  have heq := boundedField_solution_unique g hgK hd
    (boundedFlow_hasDerivAt g hgK hgL (A x)) (by simp only [boundedFlow_zero])
  exact congrFun heq t

end PoincareConjecture.M25.Topology3D
