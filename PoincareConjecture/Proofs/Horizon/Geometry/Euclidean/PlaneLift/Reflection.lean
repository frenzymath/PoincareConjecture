import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Geometry.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] {v : E}

def heightReflection (hv : ‖v‖ = 1) :
    Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ :=
  liftPlaneDiffeomorph hv 0 (-1) (by norm_num)
    (Diffeomorph.refl 𝓘(Real, (Real ∙ v)ᗮ) (Real ∙ v)ᗮ ∞)

@[simp] theorem inner_heightReflection (hv : ‖v‖ = 1) (x : E) :
    inner Real v (heightReflection hv x) = -inner Real v x := by
  exact (inner_liftPlaneDiffeomorph hv 0 (-1) (by norm_num) _ x).trans (by ring)

@[simp] theorem projection_heightReflection (hv : ‖v‖ = 1) (x : E) :
    (Real ∙ v)ᗮ.orthogonalProjectionOnto (heightReflection hv x) =
      (Real ∙ v)ᗮ.orthogonalProjectionOnto x := by
  exact projection_liftPlaneDiffeomorph hv 0 (-1) (by norm_num) _ x

@[simp] theorem heightReflection_heightReflection (hv : ‖v‖ = 1) (x : E) :
    heightReflection hv (heightReflection hv x) = x := by
  apply (heightCoordinates hv).symm.injective
  apply Prod.ext
  · change inner Real v (heightReflection hv (heightReflection hv x)) = inner Real v x
    simp
  · change (Real ∙ v)ᗮ.orthogonalProjectionOnto (heightReflection hv (heightReflection hv x)) =
      (Real ∙ v)ᗮ.orthogonalProjectionOnto x
    simp

@[simp] theorem heightReflection_height_add_plane (hv : ‖v‖ = 1)
    (t : Real) (x : (Real ∙ v)ᗮ) :
    heightReflection hv (t • v + (x : E)) = (-t) • v + (x : E) := by
  rw [heightReflection, liftPlaneDiffeomorph_apply]
  simp [inner_add_right, inner_smul_right, hv,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self v)]

@[simp] theorem heightReflection_liftPlaneDiffeomorph (hv : ‖v‖ = 1)
    (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
      (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞) (x : E) :
    heightReflection hv (liftPlaneDiffeomorph hv c s hs A x) =
      liftPlaneDiffeomorph hv (-c) (-s) (neg_ne_zero.mpr hs) A x := by
  rw [liftPlaneDiffeomorph_apply, heightReflection_height_add_plane,
    liftPlaneDiffeomorph_apply]
  congr 2
  ring

theorem image_heightReflection_liftPlaneDiffeomorph (hv : ‖v‖ = 1)
    (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
      (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞) (S : Set E) :
    heightReflection hv '' (liftPlaneDiffeomorph hv c s hs A '' S) =
      liftPlaneDiffeomorph hv (-c) (-s) (neg_ne_zero.mpr hs) A '' S := by
  rw [image_image]
  apply image_congr
  intro x _
  exact heightReflection_liftPlaneDiffeomorph hv c s hs A x

end Poincare.Geometry.Euclidean
