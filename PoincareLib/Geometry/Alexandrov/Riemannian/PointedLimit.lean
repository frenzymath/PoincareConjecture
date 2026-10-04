import PoincareLib.Geometry.Alexandrov.Riemannian.LowerCurvature
import PoincareLib.Geometry.Alexandrov.PointedLimit
import PoincareLib.Geometry.Riemannian.Compactness.Packing

/-!
# Alexandrov lower curvature of pointed Riemannian limits

Complete connected manifolds with sectional curvature at least minus one
satisfy hyperbolic four-point comparison. Its metric stability gives the
same comparison on every pointed limit, without noncollapse or a sectional
upper bound.

References: BGP (1992), Definition 2.3, p. 5, Example 2.9(1), p. 7,
Theorem 3.2, p. 8; Petrunin (2009), Section 1.5, p. 3.
-/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT.RiemannianMetric

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

end PoincareMT.RiemannianMetric
