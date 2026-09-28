import PoincareConjecture.Proofs.M76.Mathlib.OrthogonalKernelProjection
import PoincareConjecture.Proofs.M76.Mathlib.BasisEvaluation










set_option autoImplicit false

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]




@[ext] structure EuclideanSubspace where

  subspace : Submodule ℝ E

variable [FiniteDimensional ℝ E]




noncomputable instance EuclideanSubspace.instTopologicalSpace :
    TopologicalSpace (EuclideanSubspace E) :=
  TopologicalSpace.induced (fun K : EuclideanSubspace E => K.subspace.starProjection)
    inferInstance



theorem EuclideanSubspace.continuous_projector :
    Continuous (fun K : EuclideanSubspace E => K.subspace.starProjection) :=
  continuous_induced_dom

variable {E}



theorem EuclideanSubspace.continuous_iff_projector {X : Type*} [TopologicalSpace X]
    {f : X → EuclideanSubspace E} :
    Continuous f ↔ Continuous (fun x => (f x).subspace.starProjection) :=
  continuous_induced_rng



theorem EuclideanSubspace.projector_injective :
    Function.Injective (fun K : EuclideanSubspace E => K.subspace.starProjection) := by
  intro K L he
  apply EuclideanSubspace.ext
  have h := congrArg (fun Q : E →L[ℝ] E => Q.range) he
  simpa only [Submodule.range_starProjection] using h





theorem EuclideanSubspace.continuous_iff_projector_coordinates
    {ι X : Type*} [Finite ι] [TopologicalSpace X] (b : Module.Basis ι ℝ E)
    {f : X → EuclideanSubspace E} :
    Continuous f ↔ ∀ i j, Continuous (fun x => b.repr ((f x).subspace.starProjection (b i)) j) := by
  classical
  let := Fintype.ofFinite ι
  rw [continuous_iff_projector]
  constructor
  · intro h i j
    exact (continuous_apply j).comp (b.equivFunL.continuous.comp (h.clm_apply continuous_const))
  · intro h
    have hvec : ∀ i, Continuous (fun x => (f x).subspace.starProjection (b i)) := by
      intro i
      have hc : Continuous (fun x => b.equivFunL ((f x).subspace.starProjection (b i))) :=
        continuous_pi (fun j => h i j)
      simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
        b.equivFunL.symm.continuous.comp hc
    have he : Continuous (fun x => b.evaluationContinuousLinearEquiv
        (f x).subspace.starProjection) := by
      apply continuous_pi
      intro i
      simpa only [Module.Basis.evaluationContinuousLinearEquiv_apply] using hvec i
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      b.evaluationContinuousLinearEquiv.symm.continuous.comp he

end Geometry
