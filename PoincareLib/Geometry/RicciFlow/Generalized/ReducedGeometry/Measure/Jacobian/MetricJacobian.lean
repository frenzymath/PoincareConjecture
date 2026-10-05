import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian.GramDeterminant

/-!
# Metric and coordinate endpoint Jacobians

The Jacobian in Morgan-Tian Lemma 6.71, p. 141, written in the actual
earlier-slice tangent space. The equality uses only the target basis's
orthonormality for the specified slice metric.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
  {H : M14StableSet G T τ x E}

/-- The actual Gram and coordinate Jacobians coincide in an orthonormal
target basis, as used in Morgan-Tian Lemma 6.71, p. 141. -/
theorem metricJacobian_eq_coordinateJacobian
    (sourceBasis : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (targetBasis : ∀ Z : G.Horizontal x, Z ∈ H.carrier →
      Module.Basis (Fin n) ℝ
        (TangentSpace (𝓡 n) (H.endpoint_slice_map Z)))
    (horth : ∀ Z hZ i j,
      (G.slices (T - τ)).metricOnPoints.inner (H.endpoint_slice_map Z)
        (targetBasis Z hZ i) (targetBasis Z hZ j) = if i = j then 1 else 0)
    (Z : G.Horizontal x) (hZ : Z ∈ H.carrier) :
    M14MetricJacobianFromBasis G sourceBasis targetBasis Z hZ =
      M14CoordinateJacobianFromBasis G sourceBasis targetBasis Z hZ := by
  exact LinearMap.BilinForm.sqrt_max_det_comp_eq_abs_det_toMatrix
    sourceBasis (targetBasis Z hZ)
    ((G.slices (T - τ)).metricOnPoints.inner
      (H.endpoint_slice_map Z)).toBilinForm
    (horth Z hZ) (M14EndpointTangentDifferential G Z hZ).toLinearMap

end PoincareMT.M14
