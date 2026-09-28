import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.LowerCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.PointedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.Packing

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

theorem curvatureGEnegOne_of_sectional_pointed_limit
    {n : ℕ} {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    (g : ∀ j, RiemannianMetric n (M j)) (p : ∀ j, M j)
    (D : ∀ j, LeviCivitaData (g j))
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    {Y : Poincare.GromovHausdorff.BasedMetricSpaceBundle}
    (hlim : Poincare.GromovHausdorff.PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y) :
    Poincare.Alexandrov.CurvatureGEnegOne Y.carrier := by
  exact Poincare.Alexandrov.curvatureGEnegOne_of_pointedGHConvergesUnbounded
    (fun j => (g j).curvatureGEnegOne_of_sectional_lower_bound (D j) (hcomplete j) (hsec j))
    hlim

end PoincareConjecture.RiemannianMetric
