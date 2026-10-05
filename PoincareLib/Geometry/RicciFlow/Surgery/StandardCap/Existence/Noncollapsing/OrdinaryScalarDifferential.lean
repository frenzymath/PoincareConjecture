import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.OrdinaryProductCurvature
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.ConnectionScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.FixedExtension
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.RicciRegularity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.RiemannRegularity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeClosure
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Evolution.Scalar.SpatialCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Curvature.IntrinsicCalculus

/-!
# The actual scalar differential on the ordinary product

Scalar transport first gives a smooth scalar function on the retained
spacetime. Its chain rule through each actual spatial slice then transports
the differential, including included physical-time endpoints.
Source: Morgan-Tian Proposition 12.13, pp. 304-306; section 6 of
`proof-work/tasks/M34/derivations/ordinary-square-survival.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}

/-- The transported scalar is genuinely smooth on the retained
spacetime, including its time boundary (Proposition 12.13). -/
theorem ordinaryProduct_scalar_smooth (R : OrdinaryProductRicciGeometry F.metric I) :
    ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (fun z : R.product.spacetime.Point => horizontalScalarCurvature R.leafwiseConnection z) := by
  have ht : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      R.product.spacetime.timeFunction := R.product.spacetime.time_smooth
  have hc := F.contMDiffOn_scalarCurvature.comp_contMDiff
    (ht.prodMk (ordinaryProductProjection_contMDiff R.product))
    (fun z => ⟨z.1.property, mem_univ _⟩)
  apply hc.congr
  intro z
  have heq := ordinaryProduct_scalar_eq R F.connection z.1 z.2
  rw [R.product.productCylinder_eq] at heq
  change horizontalScalarCurvature R.leafwiseConnection z =
    (F.connection z.1.val).scalarCurvature (ordinaryProductProjection R.product z)
  rw [ordinaryProductProjection_eq]
  exact heq.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual horizontal scalar differential agrees with the ordinary
slice differential under the retained spatial tangent equivalence
(Proposition 12.13, pp. 304-306). -/
theorem ordinaryProduct_scalarDifferential
    (R : OrdinaryProductRicciGeometry F.metric I)
    (t : (R.product.timeIntervals.interval I).Point) (x : M) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (spacetimeModel n)
      (fun z : R.product.spacetime.Point => horizontalScalarCurvature R.leafwiseConnection z)
      (R.product.productCylinder.toSpacetime (t, x))
      (R.product.productMetric.spatialTangentEquiv t x v).val =
      mvfderiv (𝓡 n) ((F.connection t.val).scalarCurvature) x v := by
  have heq : (fun z : R.product.spacetime.Point =>
      horizontalScalarCurvature R.leafwiseConnection z) ∘
      (fun y : M => R.product.productCylinder.toSpacetime (t, y)) =
      (F.connection t.val).scalarCurvature :=
    funext (fun y => (ordinaryProduct_scalar_eq R F.connection t y).symm)
  have hs := R.product.productCylinder.smooth.comp
    ((contMDiff_const (c := t)).prodMk contMDiff_id)
  change ContMDiff (𝓡 n) (spacetimeModel n) ∞
    (fun y : M => R.product.productCylinder.toSpacetime (t, y)) at hs
  have hd := mvfderiv_comp x
    ((ordinaryProduct_scalar_smooth R).mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))
  rw [heq] at hd
  have hv := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L v) hd
  change mvfderiv (𝓡 n) ((F.connection t.val).scalarCurvature) x v =
    mvfderiv (spacetimeModel n)
      (fun z : R.product.spacetime.Point => horizontalScalarCurvature R.leafwiseConnection z)
      (R.product.productCylinder.toSpacetime (t, x))
      (mfderiv (𝓡 n) (spacetimeModel n)
        (fun y : M => R.product.productCylinder.toSpacetime (t, y)) x v) at hv
  rw [← R.product.productMetric.spatialTangentEquiv_eq] at hv
  exact hv.symm

end PoincareMT.M34
