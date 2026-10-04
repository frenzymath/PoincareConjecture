import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedVolume
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Transport.EuclideanChart
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Measure.Transport.PullbackJacobian

/-!
# The frozen metric Jacobian is the calibrated pullback Jacobian

Morgan-Tian Lemma 6.71, p. 141. The Euclidean chart uses the same source
basis as the frozen M14 metric Jacobian, and its actual derivative gives
the same Gram entries. This connects to the lower M10 calibrated area formula.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

/-- The lower calibrated pullback Jacobian is exactly the frozen M14 Gram
Jacobian in the chosen source basis, Morgan-Tian Lemma 6.71, p. 141. -/
theorem pullbackJacobian_eq_metricJacobian (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (c : ∀ Z : G.Horizontal x, Z ∈ H.carrier →
      Module.Basis (Fin n) ℝ
        (TangentSpace (𝓡 n) (H.endpoint_slice_map Z)))
    (z : EuclideanSpace ℝ (Fin n)) (hz : b.euclideanCoordinates z ∈ H.carrier) :
    M10.pullbackJacobian (G.slices (T - τ)).metricOnPoints
        (stableCoordinateChart H b) z =
      M14MetricJacobianFromBasis G b c (b.euclideanCoordinates z) hz := by
  unfold M10.pullbackJacobian M14MetricJacobianFromBasis
  rw [max_comm, ← Real.sq_sqrt', Real.sqrt_sq (Real.sqrt_nonneg _)]
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  funext i j
  change (G.slices (T - τ)).metricOnPoints.inner (stableCoordinateChart H b z)
    (mfderiv (𝓡 n) (𝓡 n) (stableCoordinateChart H b) z
      (EuclideanSpace.basisFun (Fin n) ℝ i))
    (mfderiv (𝓡 n) (𝓡 n) (stableCoordinateChart H b) z
      (EuclideanSpace.basisFun (Fin n) ℝ j)) = _
  rw [stableCoordinateChart_differential H b z hz,
    stableCoordinateChart_differential H b z hz,
    Module.Basis.euclideanCoordinates_basis, Module.Basis.euclideanCoordinates_basis]
  rfl

end PoincareMT.M14
