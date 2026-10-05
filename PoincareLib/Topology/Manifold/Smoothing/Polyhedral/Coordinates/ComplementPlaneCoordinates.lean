import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EuclideanPlaneTopology
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FrameProjectionFormula

/-!
# Complementary planes and normalized projection coordinates

Planes complementary to a fixed coordinate subspace are homeomorphic
to linear retractions onto that subspace. The plane topology is given
by orthogonal projectors; continuity in both directions follows from
the geometric kernel and frame formulas. See Cairns 1940, Lemma 5.1,
p. 801, and M76 derivation 28.
-/

set_option autoImplicit false

open Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Complements of a fixed coordinate plane with their geometric
subspace topology. See Cairns p. 801 and M76 derivation 28. -/
abbrev ComplementPlaneSpace (U : Submodule ℝ E) :=
  {K : EuclideanSubspace E // IsCompl U K.subspace}

/-- Continuous linear projections fixing the prescribed coordinate
plane pointwise, with the operator topology.
See Cairns p. 801 and M76 derivation 28. -/
abbrev RetractionSpace (U : Submodule ℝ E) :=
  {Q : E →L[ℝ] U // ∀ u : U, Q u = u}

/-- A complementary plane determines the linear retraction along it.
See Cairns p. 801 and M76 derivation 28. -/
noncomputable def complementRetraction (U : Submodule ℝ E) (K : U.ComplementPlaneSpace) :
    U.RetractionSpace :=
  ⟨(U.projectionOnto K.val.subspace K.property).toContinuousLinearMap,
    fun u => projectionOnto_apply_left K.property u⟩

/-- The retraction along a complementary plane has exactly that
kernel. See Cairns p. 801 and M76 derivation 28. -/
theorem ker_complementRetraction (U : Submodule ℝ E) (K : U.ComplementPlaneSpace) :
    (U.complementRetraction K).val.ker = K.val.subspace :=
  ker_projectionOnto K.property

/-- A normalized projection has a complementary kernel.
See Cairns p. 801 and M76 derivation 28. -/
def retractionKernel (U : Submodule ℝ E) (Q : U.RetractionSpace) : U.ComplementPlaneSpace :=
  ⟨⟨Q.val.ker⟩, LinearMap.isCompl_of_proj Q.property⟩

/-- Passing from a complementary plane to its projection and back
recovers the geometric plane. See Cairns p. 801 and M76 derivation 28. -/
theorem retractionKernel_complementRetraction (U : Submodule ℝ E)
    (K : U.ComplementPlaneSpace) : U.retractionKernel (U.complementRetraction K) = K := by
  apply Subtype.ext
  apply EuclideanSubspace.ext
  exact U.ker_complementRetraction K

/-- Passing from a projection to its kernel and back recovers the
normalized projection. See Cairns p. 801 and M76 derivation 28. -/
theorem complementRetraction_retractionKernel (U : Submodule ℝ E)
    (Q : U.RetractionSpace) : U.complementRetraction (U.retractionKernel Q) = Q := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun L : E →ₗ[ℝ] U => L x)
    (Q.val.toLinearMap.projectionOnto_of_proj Q.property)

/-- The kernel map is continuous in orthogonal-projector topology.
Every retraction is surjective by its fixed-plane identity.
See Cairns pp. 800--801 and M76 derivation 28. -/
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

/-- The retraction associated with a plane is its fixed-frame Gram
formula in the plane's geometric projector coordinates.
See Cairns p. 801 and M76 derivation 28. -/
theorem complementRetraction_eq_frameFormula (U : Submodule ℝ E)
    (K : U.ComplementPlaneSpace) :
    (U.complementRetraction K).val =
      ContinuousLinearMap.frameProjectionFormula U.subtypeL K.val.subspace.starProjection := by
  have he := (U.complementRetraction K).val.frameProjectionFormula_ker U.subtypeL
    (U.complementRetraction K).property
  simpa only [U.ker_complementRetraction K] using he.symm

/-- The inverse kernel correspondence is continuous in the actual
plane topology, including for a nonorthogonal complement.
See Cairns p. 801 and M76 derivation 28. -/
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

/-- Complementary planes and normalized projections are homeomorphic
with their geometric and operator topologies respectively.
See Cairns Lemma 5.1, p. 801, and M76 derivation 28. -/
noncomputable def complementPlaneHomeomorph (U : Submodule ℝ E) :
    U.ComplementPlaneSpace ≃ₜ U.RetractionSpace where
  toFun := U.complementRetraction
  invFun := U.retractionKernel
  left_inv := U.retractionKernel_complementRetraction
  right_inv := U.complementRetraction_retractionKernel
  continuous_toFun := U.continuous_complementRetraction
  continuous_invFun := U.continuous_retractionKernel

end Submodule
