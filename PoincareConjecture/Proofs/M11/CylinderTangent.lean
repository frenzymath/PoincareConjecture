import PoincareConjecture.Proofs.M11.KernelLinear
import PoincareConjecture.Definitions.M11CompatibleEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Algebra.Module.FiniteDimension





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {D : SmoothSpacetimeInterval K}
  {C : Type*} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C]

noncomputable def cylinderTangentEquiv (e : CompatibleSpacetimeCylinder F D C)
    (p : D.Point × C) : SpacetimeModelVector n ≃L[ℝ] SpacetimeModelVector n :=
  (LinearEquiv.ofInjectiveEndo
    (show SpacetimeModelVector n →ₗ[ℝ] SpacetimeModelVector n from
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime p).toLinearMap)
    (e.differential_injective p)).toContinuousLinearEquiv

theorem cylinder_time_chain (e : CompatibleSpacetimeCylinder F D C)
    (p : D.Point × C) (v : SpacetimeModelVector n) :
    mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction (e.toSpacetime p)
        (cylinderTangentEquiv e p v) = D.inclusionDerivative p.1 v.1 := by
  let := F.chartedSpace
  let := D.chartedSpace
  have h := mfderiv_comp_apply p
    ((F.time_smooth (e.toSpacetime p)).mdifferentiableAt (by simp))
    ((e.smooth p).mdifferentiableAt (by simp)) v
  have heq : time ∘ e.toSpacetime =
      (Subtype.val ∘ (Prod.fst : D.Point × C → D.Point)) := funext e.time_eq
  rw [heq, mfderiv_comp_apply p
    ((D.inclusion_smooth p.1).mdifferentiableAt (by simp)) mdifferentiableAt_fst,
    mfderiv_fst, ← D.inclusionDerivative_eq] at h
  exact h.symm

noncomputable def cylinderSpatialEquiv (e : CompatibleSpacetimeCylinder F D C)
    (t : D.Point) (x : C) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] F.Horizontal (e.toSpacetime (t, x)) :=
  spatialKernelEquiv (cylinderTangentEquiv e (t, x))
    (mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction (e.toSpacetime (t, x)))
    (D.inclusionDerivative t) (cylinder_time_chain e (t, x))

theorem cylinderSpatialEquiv_apply (e : CompatibleSpacetimeCylinder F D C)
    (t : D.Point) (x : C) (v : EuclideanSpace ℝ (Fin n)) :
    (cylinderSpatialEquiv e t x v).val =
      mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x) (0, v) := rfl

theorem cylinderSpatialEquiv_eq (e : CompatibleSpacetimeCylinder F D C)
    (t : D.Point) (x : C) (v : EuclideanSpace ℝ (Fin n)) :
    (cylinderSpatialEquiv e t x v).val =
      mfderiv (𝓡 n) (spacetimeModel n) (fun y : C ↦ e.toSpacetime (t, y)) x v := by
  have h := mfderiv_comp_apply x ((e.smooth (t, x)).mdifferentiableAt (by simp))
    ((contMDiff_const.prodMk contMDiff_id : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y : C ↦ (t, y))) x |>.mdifferentiableAt (by simp)) v
  rw [mfderiv_prod_right] at h
  exact h.symm

end PoincareConjecture.Proofs.M11
