import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.ComparisonAngles
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.PointedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.Packing









noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff
open Poincare.Alexandrov Poincare.GromovHausdorff

universe u

namespace PoincareConjecture.RiemannianMetric

theorem exists_comparisonAngle_packing_bound_of_sectional_pointed_limit
    (n : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ N : ℕ,
      ∀ {M : ℕ → Type u}
        [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
        [∀ j, PreconnectedSpace (M j)]
        [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
        [∀ j, IsManifold (𝓡 n) ∞ (M j)],
      ∀ (g : ∀ j, RiemannianMetric n (M j)) (p : ∀ j, M j)
        (D : ∀ j, LeviCivitaData (g j)),
        (∀ j, MetricComplete (g j)) →
        (∀ j x (v w : TangentSpace (𝓡 n) x),
          -1 ≤ (D j).sectionalCurvature x v w) →
      ∀ {Y : BasedMetricSpaceBundle.{u}},
        PointedGHConvergesUnbounded
          (fun j => (g j).toBasedMetricSpace (p j)) Y →
        ComparisonAnglePackingBound Y.carrier α N := by
  obtain ⟨N, hN⟩ := exists_comparisonAngle_packing_bound n hα
  refine ⟨N, ?_⟩
  intro M _ _ _ _ _ g p D hcomplete hsec Y hlim
  apply comparisonAnglePackingBound_of_pointedGHConvergesUnbounded (X :=
    fun j => (g j).toBasedMetricSpace (p j)) (h := hlim)
  intro j k x q hq hangle
  simpa only [Fintype.card_fin] using hN (g j) (D j) (hcomplete j) (hsec j)
    x q hq (fun i l hil => (hangle i l hil).le)

end PoincareConjecture.RiemannianMetric
