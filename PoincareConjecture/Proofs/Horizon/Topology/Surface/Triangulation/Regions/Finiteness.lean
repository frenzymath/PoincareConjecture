


import PoincareConjecture.Proofs.Horizon.Topology.Connected.FiniteComplement
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Frontier








set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]



theorem finite_regions_of_finite_local_complements
    (s : Finset M) (r : M → ℝ) (hpos : ∀ p ∈ s, 0 < r p)
    (htarget : ∀ p ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).target)
    (hcover : (⋃ p ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) (r p)) = (univ : Set M))
    (hloc : ∀ x ∈ chartDiskBoundaryUnion s r, ∃ U : Set M,
      IsOpen U ∧ x ∈ U ∧
        Finite (ConnectedComponents ((U \ chartDiskBoundaryUnion s r) : Set M))) :
    Finite (ConnectedComponents ((chartDiskBoundaryUnion s r)ᶜ : Set M)) := by
  apply Poincare.Topology.finite_connectedComponents_compl_of_locally_finite
    (isCompact_chartDiskBoundaryUnion s r htarget) _ hloc
  intro x hx
  obtain ⟨y, hy, hyK, _⟩ := exists_nonvertex_mem_frontier_complementary_component
    s r hpos htarget hcover x hx (V := ∅) finite_empty
  exact ⟨y, hy, hyK⟩

end PoincareConjecture.Topology.Surface
