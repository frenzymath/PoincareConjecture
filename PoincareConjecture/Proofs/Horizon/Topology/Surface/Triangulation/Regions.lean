import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartCover
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

def chartDiskBoundaryUnion (s : Finset M) (r : M → ℝ) : Set M :=
  ⋃ p ∈ s, frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
    closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p))

variable [T2Space M]

theorem exists_chart_disk_containing_complementary_component
    (s : Finset M) (r : M → ℝ) (hpos : ∀ p ∈ s, 0 < r p)
    (htarget : ∀ p ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).target)
    (hcover : (⋃ p ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p)) = (univ : Set M))
    (x : M) (hx : x ∉ chartDiskBoundaryUnion s r) :
    ∃ p ∈ s,
      connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
          ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) ∧
      closure (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
          closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) ∧
      IsCompact (closure (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x)) ∧
      closure (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).source := by
  have hxcover : x ∈ ⋃ p ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) := by
    rw [hcover]
    exact mem_univ x
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxcover
  have hinterior : interior ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p)) =
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) := by
    rw [interior_chart_image p (htarget p hp), interior_closedBall _ (hpos p hp).ne']
  have hcomponent : connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) := by
    rw [← hinterior]
    apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      isPreconnected_connectedComponentIn
    · apply disjoint_left.mpr
      intro y hy hyfront
      exact connectedComponentIn_subset (chartDiskBoundaryUnion s r)ᶜ x hy
        (mem_iUnion₂.mpr ⟨p, hp, hyfront⟩)
    · exact ⟨x, mem_connectedComponentIn hx, hinterior.symm ▸ hxp⟩
  have hclosure : closure (connectedComponentIn (chartDiskBoundaryUnion s r)ᶜ x) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
        closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) := by
    rw [← closure_chart_ball p (hpos p hp) (htarget p hp)]
    exact closure_mono hcomponent
  exact ⟨p, hp, hcomponent, hclosure,
    (isCompact_chart_closedBall p (htarget p hp)).of_isClosed_subset isClosed_closure hclosure,
    hclosure.trans (chart_closedBall_subset_source p (htarget p hp))⟩

end PoincareConjecture.Topology.Surface
