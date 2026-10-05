/-
Copyright (c) 2026 The PoincareLib contributors.
-/
import PoincareLib.Topology.Connected.FiniteComplement
import PoincareLib.Topology.Surface.Triangulation.Regions.Frontier

/-!
# Finiteness of complementary surface regions

For the boundaries of a coordinate disk cover, global finiteness follows from
finite local complementary sectors: the boundary union is compact, and every
complementary region meets it.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareMT.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- Finite local complements along coordinate disk boundaries imply finitely
many complementary regions of the entire surface boundary arrangement. -/
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

end PoincareMT.Topology.Surface
