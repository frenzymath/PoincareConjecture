import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.LocalFiniteness
import PoincareConjecture.Proofs.Horizon.Topology.Connected.ClosureCover

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

theorem dense_compl_chartDiskBoundaryUnion (s : Finset M) (r : M → ℝ)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    Dense (chartDiskBoundaryUnion s r)ᶜ :=
  Poincare.Topology.dense_compl_finite_frontier_union s
    (fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x))
    (fun x hx => (isCompact_chart_closedBall x (htarget x hx)).isClosed)

variable [IsManifold (𝓡 2) ∞ M]

theorem exists_finite_region_closure_cover_of_chart_circle_general_position
    (s : Finset M) (r : M → ℝ) (hpos : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hcover : (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x)) = (univ : Set M))
    (htriple : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
      ∀ p ∈ chartCircle x (r x), p ∈ chartCircle y (r y) →
        p ∉ chartCircle z (r z))
    (hregular : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ChartCircleRegularAlong x (r x) y (r y) ∨
        ChartCircleRegularAlong y (r y) x (r x)) :
    ∃ R : Finset M, (∀ x ∈ R, x ∉ chartDiskBoundaryUnion s r) ∧
      (∀ x ∈ R, ∀ y ∈ R,
        connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x =
          connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ y → x = y) ∧
      (⋃ x ∈ R, closure (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x)) = univ := by
  have : Finite (ConnectedComponents ((chartDiskBoundaryUnion s r)ᶜ : Set M)) :=
    finite_regions_of_chart_circle_general_position s r hpos htarget hcover htriple hregular
  exact Poincare.Topology.exists_finite_component_closure_cover_of_dense
    (S := (chartDiskBoundaryUnion s r)ᶜ)
    (dense_compl_chartDiskBoundaryUnion s r htarget)

end PoincareConjecture.Topology.Surface
