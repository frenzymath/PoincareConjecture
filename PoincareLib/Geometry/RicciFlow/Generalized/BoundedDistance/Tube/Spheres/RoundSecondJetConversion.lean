import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Spheres.RoundMetricDerivatives
import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.BundleContact
import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Radial

/-!
# Second ordinary jet at a normal point

At a Gauss centre the model connection itself vanishes.  The second ordinary
derivative of a tensor section therefore differs from the second covariant
derivative by one term: the first derivative of the connection acting on the
zeroth-order tensor.  This file keeps that term explicit and supplies the
corresponding norm estimate.  The result is local and is not an atlas-wide
coordinate-control assertion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped ContDiff Bundle BigOperators Topology Manifold

namespace PoincareMT.M28.tube

open Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "covDer" => Poincare.Riemannian.RadialTransport.covariantDerivative

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
private lemma covDer_contDiffAt
    {Γ : E → E →L[ℝ] F →L[ℝ] F} {S : E → F}
    {x : E} (hΓ : ContDiffAt ℝ ∞ Γ x) (hS : ContDiffAt ℝ ∞ S x)
    (v : E) :
    ContDiffAt ℝ ∞ (fun y => covDer Γ S y v) x := by
  exact ((hS.fderiv_right (by simp)).clm_apply contDiffAt_const).add
    ((hΓ.clm_apply contDiffAt_const).clm_apply hS)

/- The exact identity is stated before taking norms.  At `x`, the zeroth
connection term is killed by `hzero`; the remaining product derivative is
the derivative of the connection acting on `S x`. -/
omit [FiniteDimensional ℝ E] [CompleteSpace F] in
omit [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem second_fderiv_eq_covariant_sub_connectionJet
    {Γ : E → E →L[ℝ] F →L[ℝ] F} {S : E → F} {x : E}
    (hΓ : ContDiffAt ℝ ∞ Γ x) (hS : ContDiffAt ℝ ∞ S x)
    (hzero : Γ x = 0) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ S y v) x u =
      covDer Γ (fun y => covDer Γ S y v) x u -
        (fderiv ℝ Γ x u) v (S x) := by
  let A : E → F := fun y => covDer Γ S y v
  have hΓd : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by simp)
  have hSd : DifferentiableAt ℝ S x := hS.differentiableAt (by simp)
  have hfd : ContDiffAt ℝ ∞ (fun y => fderiv ℝ S y v) x :=
    (hS.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hconn : ContDiffAt ℝ ∞ (fun y => Γ y v (S y)) x :=
    (hΓ.clm_apply contDiffAt_const).clm_apply hS
  have hsum : A =
      (fun y => fderiv ℝ S y v) + (fun y => Γ y v (S y)) := by
    funext y
    rfl
  have hA : ContDiffAt ℝ ∞ A x := covDer_contDiffAt hΓ hS v
  have hprod : fderiv ℝ (fun y => Γ y v (S y)) x u =
      (fderiv ℝ Γ x u) v (S x) := by
    rw [fderiv_clm_apply (hΓd.clm_apply (differentiableAt_const (c := v))) hSd,
      fderiv_clm_apply hΓd (differentiableAt_const (c := v))]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, add_apply, hzero, zero_apply, zero_add]
  have hadd := fderiv_fun_add (hfd.differentiableAt (by simp))
    (hconn.differentiableAt (by simp))
  have hAder : fderiv ℝ A x u =
      fderiv ℝ (fun y => fderiv ℝ S y v) x u +
        fderiv ℝ (fun y => Γ y v (S y)) x u := by
    change fderiv ℝ (fun y => A y) x u = _
    rw [hsum]
    exact congrArg (fun L => L u) hadd
  have hcov : covDer Γ A x u = fderiv ℝ A x u := by
    change fderiv ℝ A x u + Γ x u (A x) = fderiv ℝ A x u
    simp only [hzero, zero_apply, add_zero]
  rw [hcov, hAder, hprod]
  abel

/- A norm form suited to the metric error: the covariant second jet and the
connection first jet are independent inputs, while the zeroth tensor norm is
multiplied by them exactly as in the product rule above. -/
omit [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem norm_second_fderiv_le_of_zero_connection
    {Γ : E → E →L[ℝ] F →L[ℝ] F} {S : E → F} {x : E}
    (hΓ : ContDiffAt ℝ ∞ Γ x) (hS : ContDiffAt ℝ ∞ S x)
    (hzero : Γ x = 0) (u v : E) {A G V W : ℝ}
    (hA : ‖covDer Γ (fun y => covDer Γ S y v) x u‖ ≤ A)
    (hG : ‖fderiv ℝ Γ x u‖ ≤ G)
    (hV : ‖v‖ ≤ V) (hW : ‖S x‖ ≤ W)
    (_hA0 : 0 ≤ A) (hG0 : 0 ≤ G) (hV0 : 0 ≤ V) (_hW0 : 0 ≤ W) :
    ‖fderiv ℝ (fun y => fderiv ℝ S y v) x u‖ ≤ A + G * V * W := by
  rw [second_fderiv_eq_covariant_sub_connectionJet hΓ hS hzero u v]
  calc
    ‖covDer Γ (fun y => covDer Γ S y v) x u - (fderiv ℝ Γ x u) v (S x)‖ ≤
        ‖covDer Γ (fun y => covDer Γ S y v) x u‖ +
          ‖(fderiv ℝ Γ x u) v (S x)‖ := norm_sub_le _ _
    _ ≤ A + (G * ‖v‖) * ‖S x‖ := by
      have hv' : ‖(fderiv ℝ Γ x u) v‖ ≤ G * ‖v‖ :=
        (ContinuousLinearMap.le_opNorm (fderiv ℝ Γ x u) v).trans
          (mul_le_mul_of_nonneg_right hG (norm_nonneg v))
      have hS' : ‖(fderiv ℝ Γ x u) v (S x)‖ ≤
          (G * ‖v‖) * ‖S x‖ :=
        (ContinuousLinearMap.le_opNorm ((fderiv ℝ Γ x u) v) (S x)).trans
          (mul_le_mul_of_nonneg_right hv' (norm_nonneg (S x)))
      exact add_le_add hA hS'
    _ ≤ A + G * V * W := by
      gcongr

end PoincareMT.M28.tube
