import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Manifold.Diffeomorph



noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace Poincare.Geometry.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] {v : E}



def heightCoordinates (hv : ‖v‖ = 1) : (Real × (Real ∙ v)ᗮ) ≃L[Real] E :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun z => z.1 • v + (z.2 : E)
    invFun := fun x => (inner Real v x, (Real ∙ v)ᗮ.orthogonalProjectionOnto x)
    left_inv := by
      intro z
      apply Prod.ext
      · simp [inner_add_right, inner_smul_right, hv,
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2.property]
      · simp
    right_inv := by
      intro x
      nth_rw 2 [← (Real ∙ v).starProjection_add_starProjection_orthogonal x]
      rw [Submodule.starProjection_unit_singleton Real hv]
      rfl
    map_add' := by
      intro z w
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
      abel
    map_smul' := by
      intro a z
      simp [smul_add, smul_smul] }

@[simp] theorem heightCoordinates_apply (hv : ‖v‖ = 1) (t : Real) (x : (Real ∙ v)ᗮ) :
    heightCoordinates hv (t, x) = t • v + (x : E) := rfl

@[simp] theorem heightCoordinates_symm_apply (hv : ‖v‖ = 1) (x : E) :
    (heightCoordinates hv).symm x =
      (inner Real v x, (Real ∙ v)ᗮ.orthogonalProjectionOnto x) := rfl

@[simp] theorem inner_heightCoordinates (hv : ‖v‖ = 1) (z : Real × (Real ∙ v)ᗮ) :
    inner Real v (heightCoordinates hv z) = z.1 :=
  congrArg Prod.fst ((heightCoordinates hv).symm_apply_apply z)

end Poincare.Geometry.Euclidean
