import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Geometry.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] (v : E)

omit [FiniteDimensional Real E] in
theorem orthogonal_axis_neg : (Real ∙ v)ᗮ = (Real ∙ (-v))ᗮ := by
  congr 1
  simpa only [Set.neg_singleton] using (Submodule.span_neg (R := Real) ({v} : Set E)).symm

def axisNegPlaneEquiv : (Real ∙ v)ᗮ ≃ₗᵢ[Real] (Real ∙ (-v))ᗮ :=
  LinearIsometryEquiv.ofEq _ _ (orthogonal_axis_neg v)

omit [FiniteDimensional Real E] in
@[simp] theorem coe_axisNegPlaneEquiv (x : (Real ∙ v)ᗮ) :
    (axisNegPlaneEquiv v x : E) = (x : E) := rfl

omit [FiniteDimensional Real E] in
@[simp] theorem coe_axisNegPlaneEquiv_symm (x : (Real ∙ (-v))ᗮ) :
    ((axisNegPlaneEquiv v).symm x : E) = (x : E) := rfl

omit [FiniteDimensional Real E] in
theorem axisNegPlaneEquiv_projection (x : E) :
    axisNegPlaneEquiv v ((Real ∙ v)ᗮ.orthogonalProjectionOnto x) =
      (Real ∙ (-v))ᗮ.orthogonalProjectionOnto x := by
  apply Subtype.ext
  rw [coe_axisNegPlaneEquiv]
  simp only [Submodule.coe_orthogonalProjectionOnto_apply, orthogonal_axis_neg v]

def axisNegPlaneDiffeomorph
    (A : (Real ∙ v)ᗮ ≃ₘ[Real] (Real ∙ v)ᗮ) :
    (Real ∙ (-v))ᗮ ≃ₘ[Real] (Real ∙ (-v))ᗮ :=
  let J := (axisNegPlaneEquiv v).toContinuousLinearEquiv.toDiffeomorph
  let N := (ContinuousLinearEquiv.neg Real (M := ↥((Real ∙ v)ᗮ))).toDiffeomorph
  ((J.symm.trans N).trans A).trans J

omit [FiniteDimensional Real E] in
theorem axisNegPlaneDiffeomorph_apply_neg
    (A : (Real ∙ v)ᗮ ≃ₘ[Real] (Real ∙ v)ᗮ) (x : (Real ∙ v)ᗮ) :
    axisNegPlaneDiffeomorph v A (axisNegPlaneEquiv v (-x)) = axisNegPlaneEquiv v (A x) := by
  change axisNegPlaneEquiv v (A (-((axisNegPlaneEquiv v).symm
    (axisNegPlaneEquiv v (-x))))) = _
  rw [(axisNegPlaneEquiv v).symm_apply_apply, neg_neg]

theorem axisNegPlaneDiffeomorph_image_sphere
    (A : (Real ∙ v)ᗮ ≃ₘ[Real] (Real ∙ v)ᗮ) (r : Real) :
    axisNegPlaneDiffeomorph v A '' Metric.sphere 0 r =
      axisNegPlaneEquiv v '' (A '' Metric.sphere 0 r) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let z := -((axisNegPlaneEquiv v).symm x)
    have hz : z ∈ Metric.sphere 0 r := by
      simpa only [Metric.mem_sphere, dist_zero_right, z, norm_neg,
        (axisNegPlaneEquiv v).symm.norm_map] using hx
    refine ⟨A z, ⟨z, hz, rfl⟩, ?_⟩
    have heq : axisNegPlaneEquiv v (-z) = x := by
      simp only [z, neg_neg, (axisNegPlaneEquiv v).apply_symm_apply]
    rw [← axisNegPlaneDiffeomorph_apply_neg, heq]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨axisNegPlaneEquiv v (-x), ?_, axisNegPlaneDiffeomorph_apply_neg v A x⟩
    simpa only [Metric.mem_sphere, dist_zero_right, (axisNegPlaneEquiv v).norm_map,
      norm_neg] using hx

omit [FiniteDimensional Real E] in
theorem axisNegPlaneDiffeomorph_projection_neg
    (A : (Real ∙ v)ᗮ ≃ₘ[Real] (Real ∙ v)ᗮ) (x : E) :
    (axisNegPlaneDiffeomorph v A ((Real ∙ (-v))ᗮ.orthogonalProjectionOnto (-x)) : E) =
      (A ((Real ∙ v)ᗮ.orthogonalProjectionOnto x) : E) := by
  rw [← axisNegPlaneEquiv_projection]
  rw [map_neg]
  change (axisNegPlaneEquiv v
    (A (-((axisNegPlaneEquiv v).symm (axisNegPlaneEquiv v
      (-((Real ∙ v)ᗮ.orthogonalProjectionOnto x)))))) : E) = _
  rw [(axisNegPlaneEquiv v).symm_apply_apply, neg_neg, coe_axisNegPlaneEquiv]

theorem liftPlaneDiffeomorph_axis_neg (hv : ‖v‖ = 1)
    (c s : Real) (hs : s ≠ 0) (A : (Real ∙ v)ᗮ ≃ₘ[Real] (Real ∙ v)ᗮ) (x : E) :
    liftPlaneDiffeomorph (by simpa using hv : ‖-v‖ = 1)
        (-c) (-s) (neg_ne_zero.mpr hs) (axisNegPlaneDiffeomorph v A) (-x) =
      liftPlaneDiffeomorph hv c s hs A x := by
  rw [liftPlaneDiffeomorph_apply, liftPlaneDiffeomorph_apply,
    axisNegPlaneDiffeomorph_projection_neg, inner_neg_neg, smul_neg]
  congr 1
  rw [← neg_smul]
  congr 1
  ring

end Poincare.Geometry.Euclidean
