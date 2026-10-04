import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Positive.PositiveHistoryComponent
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.ScalarGradientNorm
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.QuotientHomothety
import PoincareLib.Geometry.Riemannian.Curvature.Scalar.Regularity
import PoincareLib.Geometry.Manifold.OpenEmbedding
import PoincareLib.Geometry.RicciFlow.Surgery.Control.ModelBounds

/-!
# Static canonical analytics on the actual ordinary history

Spatial local isometries preserve the exact scalar, frozen scalar-gradient
norm, and scalar evolution expression. This transports the pointwise
estimate without extending a strong neck before the history's onset.
Source: Morgan--Tian, pp. 3-7, 230-231 and 393-394.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M47Positive

section Geometry

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N} {f : M → N}

/-- The frozen supremum over actual metric-unit directions is preserved
by a smooth local metric pullback; MT pp. 3-7 and Definition 9.72. -/
theorem scalarGradientNorm_eq_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (hD' : D'.CurvatureTensorCalculus)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f)
    (hmetric : ∀ y : M, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w)) (x : M) :
    scalarGradientNorm g D x = scalarGradientNorm h D' (f x) := by
  have hR : D.scalarCurvature = D'.scalarCurvature ∘ f := by
    funext y
    exact D.scalarCurvature_eq_of_local_isometry D' isOpen_univ hf.contMDiff.contMDiffOn
      (fun z _hz => hmetric z) (mem_univ y)
  have hinv : (mfderiv (𝓡 3) (𝓡 3) f x).IsInvertible :=
    ⟨hf.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩
  have hgradient := D.gradient_comp_eq_mpullback D'
    (hf.contMDiff.mdifferentiable (by simp) x)
    (hD'.contMDiff_scalarCurvature.mdifferentiable (by simp) (f x)) hinv (hmetric x)
  have hnorm : g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) =
      h.inner (f x) (D'.gradient D'.scalarCurvature (f x))
        (D'.gradient D'.scalarCurvature (f x)) := by
    rw [hR, hgradient, hmetric]
    simp only [mpullback, hinv.self_apply_inverse]
  rw [scalarGradientNorm_eq_tangentNorm, scalarGradientNorm_eq_tangentNorm]
  exact congrArg Real.sqrt hnorm

/-- The exact spatial expression supplying scalar time evolution is
preserved by the actual local metric pullback; MT equation (3.7), p. 41. -/
theorem scalarEvolution_eq_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (hD' : D'.CurvatureTensorCalculus)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f)
    (hmetric : ∀ y : M, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w)) (x : M) :
    D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x =
      D'.laplacian D'.scalarCurvature (f x) + 2 * D'.ricciNormSq (f x) := by
  have hR : D.scalarCurvature = D'.scalarCurvature ∘ f := by
    funext y
    exact D.scalarCurvature_eq_of_local_isometry D' isOpen_univ hf.contMDiff.contMDiffOn
      (fun z _hz => hmetric z) (mem_univ y)
  have hinv : ∀ y : M, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    fun y => ⟨hf.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩
  have hlap : D.laplacian D.scalarCurvature x = D'.laplacian D'.scalarCurvature (f x) := by
    rw [hR]
    exact D.laplacian_comp_of_metric_pullback D' (hf.contMDiff x)
      (Eventually.of_forall hinv) (Eventually.of_forall hmetric)
      (hD'.contMDiff_scalarCurvature (f x))
  rw [hlap, D.ricciNormSq_eq_of_local_isometry D' hD' isOpen_univ
    hf.contMDiff.contMDiffOn (fun z _hz => hmetric z) (mem_univ x)]

/-- The complete pointwise canonical analytic estimate transfers at the
identical coefficient, with no temporal neck or history premise;
Definition 9.72 and the positive-history use on pp. 393-394. -/
theorem pointwise_analytic_estimate_of_metric_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (hD' : D'.CurvatureTensorCalculus)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f)
    (hmetric : ∀ y : M, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w))
    {x : M} {A : ℝ} (hbound : M45PointwiseAnalyticEstimate h D' (f x) A) :
    M45PointwiseAnalyticEstimate g D x A := by
  have hR := D.scalarCurvature_eq_of_local_isometry D' isOpen_univ
    hf.contMDiff.contMDiffOn (fun z _hz => hmetric z) (mem_univ x)
  rw [M45PointwiseAnalyticEstimate, hR,
    scalarGradientNorm_eq_of_metric_pullback D D' hD' hf hmetric x,
    scalarEvolution_eq_of_metric_pullback D D' hD' hf hmetric x]
  exact hbound

end Geometry

/-- The actual cylinder slice transfers the physical pointwise model
estimate to its literal metric on the open source. This includes an
onset slice without supplying a longer strong-neck time interval. -/
theorem cylinder_pointwise_analytic_estimate
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (U : TopologicalSpace.Opens C.carrier)
    (e : SurgeryFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (g : RiemannianMetric 3 U) (D : LeviCivitaData g)
    (hD : (F.connection (origin + s / scale)).CurvatureTensorCalculus)
    (hmetric : ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) = g.inner y v w)
    {x : U} {A : ℝ}
    (hbound : M45PointwiseAnalyticEstimate (F.metric (origin + s / scale))
      (F.connection (origin + s / scale)) (e.forward s hs x.val) A) :
    M45PointwiseAnalyticEstimate g D x A := by
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun y : U => e.forward s hs y.val) := by
    intro y
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U y).comp
      (𝓡 3) (F.slice (origin + s / scale)).carrier
      ((M44.cylinderSliceChart e U.isOpen s hs).isLocalDiffeomorphAt
        (𝓡 3) (𝓡 3) ∞ y.property)
  exact pointwise_analytic_estimate_of_metric_pullback D
    (F.connection (origin + s / scale)) hD hf (fun y v w => (hmetric y v w).symm) hbound

end PoincareMT.M47Positive
