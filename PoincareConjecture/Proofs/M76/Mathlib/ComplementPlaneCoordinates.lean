import PoincareConjecture.Proofs.M76.Mathlib.EuclideanPlaneTopology
import PoincareConjecture.Proofs.M76.Mathlib.FrameProjectionFormula

set_option autoImplicit false

open Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev ComplementPlaneSpace (U : Submodule ℝ E) :=
  {K : EuclideanSubspace E // IsCompl U K.subspace}

abbrev RetractionSpace (U : Submodule ℝ E) :=
  {Q : E →L[ℝ] U // ∀ u : U, Q u = u}

noncomputable def complementRetraction (U : Submodule ℝ E) (K : U.ComplementPlaneSpace) :
    U.RetractionSpace :=
  ⟨(U.projectionOnto K.val.subspace K.property).toContinuousLinearMap,
    fun u => projectionOnto_apply_left K.property u⟩

theorem ker_complementRetraction (U : Submodule ℝ E) (K : U.ComplementPlaneSpace) :
    (U.complementRetraction K).val.ker = K.val.subspace :=
  ker_projectionOnto K.property

def retractionKernel (U : Submodule ℝ E) (Q : U.RetractionSpace) : U.ComplementPlaneSpace :=
  ⟨⟨Q.val.ker⟩, LinearMap.isCompl_of_proj Q.property⟩

theorem retractionKernel_complementRetraction (U : Submodule ℝ E)
    (K : U.ComplementPlaneSpace) : U.retractionKernel (U.complementRetraction K) = K := by
  apply Subtype.ext
  apply EuclideanSubspace.ext
  exact U.ker_complementRetraction K

theorem complementRetraction_retractionKernel (U : Submodule ℝ E)
    (Q : U.RetractionSpace) : U.complementRetraction (U.retractionKernel Q) = Q := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun L : E →ₗ[ℝ] U => L x)
    (Q.val.toLinearMap.projectionOnto_of_proj Q.property)

theorem continuous_retractionKernel (U : Submodule ℝ E) : Continuous U.retractionKernel := by
  apply Continuous.subtype_mk
  change Continuous (fun Q : U.RetractionSpace => (⟨Q.val.ker⟩ : EuclideanSubspace E))
  apply EuclideanSubspace.continuous_iff_projector.mpr
  change Continuous (fun Q : U.RetractionSpace => Q.val.ker.starProjection)
  have he : (fun Q : U.RetractionSpace => Q.val.ker.starProjection) =
      (fun Q => Q.val.kernelProjectionFormula) :=
    funext (fun Q => Q.val.starProjection_ker_eq_formula (fun u => ⟨u, Q.property u⟩))
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro Q
  exact (Q.val.continuousAt_kernelProjectionFormula (fun u => ⟨u, Q.property u⟩)).comp
    (f := fun R : U.RetractionSpace => R.val) continuous_subtype_val.continuousAt

theorem complementRetraction_eq_frameFormula (U : Submodule ℝ E)
    (K : U.ComplementPlaneSpace) :
    (U.complementRetraction K).val =
      ContinuousLinearMap.frameProjectionFormula U.subtypeL K.val.subspace.starProjection := by
  have he := (U.complementRetraction K).val.frameProjectionFormula_ker U.subtypeL
    (U.complementRetraction K).property
  simpa only [U.ker_complementRetraction K] using he.symm

theorem continuous_complementRetraction (U : Submodule ℝ E) :
    Continuous U.complementRetraction := by
  apply Continuous.subtype_mk
  change Continuous (fun K : U.ComplementPlaneSpace => (U.complementRetraction K).val)
  have he : (fun K : U.ComplementPlaneSpace => (U.complementRetraction K).val) =
      (fun K => ContinuousLinearMap.frameProjectionFormula U.subtypeL
        K.val.subspace.starProjection) :=
    funext (U.complementRetraction_eq_frameFormula)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro K
  have hinj : Function.Injective (ContinuousLinearMap.perpendicularFrame U.subtypeL
      K.val.subspace.starProjection) := by
    have h := (U.complementRetraction K).val.injective_perpendicularFrame_of_rightInverse
      U.subtypeL (U.complementRetraction K).property
    simpa only [U.ker_complementRetraction K] using h
  exact (ContinuousLinearMap.continuousAt_frameProjectionFormula U.subtypeL _ hinj).comp
    (f := fun K : U.ComplementPlaneSpace => K.val.subspace.starProjection)
    ((EuclideanSubspace.continuous_projector E).comp continuous_subtype_val).continuousAt

noncomputable def complementPlaneHomeomorph (U : Submodule ℝ E) :
    U.ComplementPlaneSpace ≃ₜ U.RetractionSpace where
  toFun := U.complementRetraction
  invFun := U.retractionKernel
  left_inv := U.retractionKernel_complementRetraction
  right_inv := U.complementRetraction_retractionKernel
  continuous_toFun := U.continuous_complementRetraction
  continuous_invFun := U.continuous_retractionKernel

end Submodule
