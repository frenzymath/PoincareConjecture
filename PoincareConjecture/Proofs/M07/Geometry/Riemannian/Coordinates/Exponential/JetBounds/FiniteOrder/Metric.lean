import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FiniteOrder.Frame
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.MetricJetInduction



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Poincare.Riemannian.RadialTransport
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem exists_uniform_geodesic_coordinate_metric_jet_bound
    (n m : ℕ) (r : ℝ) (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
      (∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w) →
      (∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
        christoffelBilinear g.euclideanCoefficients (t • x) x x = 0) →
      (∀ l ≤ m, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
        D.curvatureDerivativeNorm l x ≤ C l) →
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
        ‖iteratedFDeriv ℝ m g.euclideanCoefficients x‖ ≤ B := by
  obtain ⟨A, B, K, hA, hB, hK, hbound⟩ :=
    exists_uniform_radial_frame_jet_bounds_through n r C hC m m le_rfl
  refine ⟨n * scalarJetProductBound m (fun _ => A) (fun _ => A),
    mul_nonneg (Nat.cast_nonneg _) (scalarJetProductBound_nonneg ..), ?_⟩
  intro g D h0 hgeo hcurv x hx
  have hΓ : ContDiff ℝ ∞ (christoffelBilinear g.euclideanCoefficients) := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
      (g.inner_isInvertible y)
  obtain ⟨T, hT, _, hTv, hTi, _⟩ := exists_radial_transport_operator hΓ
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h := (hbound g D b h0 hgeo T hT hTi hTv hcurv).2.1
  exact norm_iteratedFDeriv_metric_le_of_coframe D b h0 hT hTi hTv m (fun _ => A) x
    (fun q hq a u => h q hq a u x hx)

end PoincareConjecture.CoordinateExponential
