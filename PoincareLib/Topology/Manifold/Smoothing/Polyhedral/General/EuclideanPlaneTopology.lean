import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.OrthogonalKernelProjection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.BasisEvaluation

/-!
# Euclidean subspaces in orthogonal-projector topology

Subspaces are topologized by their actual orthogonal projectors, the
basis-independent version of direction-cosine coordinates. This is
the plane topology of Cairns 1940, Section 4, p. 800; see M76 derivation
28. No topology is transported from normalized projection operators.
-/

set_option autoImplicit false

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A linear subspace, wrapped to specify its geometric plane
topology without assigning a global topology to all submodules.
See Cairns p. 800 and M76 derivation 28. -/
@[ext] structure EuclideanSubspace where
  /-- The underlying linear subspace; see Cairns p. 800. -/
  subspace : Submodule ℝ E

variable [FiniteDimensional ℝ E]

/-- The topology induced by orthogonal projectors, equivalently by
their matrices in any fixed orthonormal basis.
See Cairns p. 800 and M76 derivation 28. -/
noncomputable instance EuclideanSubspace.instTopologicalSpace :
    TopologicalSpace (EuclideanSubspace E) :=
  TopologicalSpace.induced (fun K : EuclideanSubspace E => K.subspace.starProjection)
    inferInstance

/-- The geometric projector coordinate map is continuous by the
specified plane topology. See Cairns p. 800 and M76 derivation 28. -/
theorem EuclideanSubspace.continuous_projector :
    Continuous (fun K : EuclideanSubspace E => K.subspace.starProjection) :=
  continuous_induced_dom

variable {E}

/-- A plane-valued family is continuous exactly when its orthogonal
projectors are continuous. See Cairns p. 800 and M76 derivation 28. -/
theorem EuclideanSubspace.continuous_iff_projector {X : Type*} [TopologicalSpace X]
    {f : X → EuclideanSubspace E} :
    Continuous f ↔ Continuous (fun x => (f x).subspace.starProjection) :=
  continuous_induced_rng

/-- Orthogonal projectors determine their subspaces, so the plane
coordinates are faithful. See Cairns p. 800 and M76 derivation 28. -/
theorem EuclideanSubspace.projector_injective :
    Function.Injective (fun K : EuclideanSubspace E => K.subspace.starProjection) := by
  intro K L he
  apply EuclideanSubspace.ext
  have h := congrArg (fun Q : E →L[ℝ] E => Q.range) he
  simpa only [Submodule.range_starProjection] using h

/-- The geometric plane topology is exactly convergence of all
projector matrix coordinates in any finite basis. In an orthonormal
basis these are direction-cosine coordinates.
See Cairns p. 800 and M76 derivation 28. -/
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
