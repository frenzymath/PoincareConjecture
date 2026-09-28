import PoincareConjecture.Proofs.M39.Mathlib.RootedSeparation
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegions
import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set



theorem IsPreconnected.m76_subset_of_disjoint_frontier {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hS : IsPreconnected S) (hU : IsOpen U)
    (hdis : Disjoint (frontier U) S) (hmeet : (S ∩ U).Nonempty) : S ⊆ U := by
  exact hS.subset_of_disjoint_frontier hU hdis.symm hmeet

namespace Polygon



theorem inside_eq_of_open_bounded_frontier {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hne : U.Nonempty) (hfront : frontier U = P.boundary ℝ) : P.inside = U := by
  have hsub : U ⊆ P.inside := by
    intro x hx
    have hxb : x ∈ (P.boundary ℝ)ᶜ := by
      rw [← hfront, frontier, hU.interior_eq]
      exact fun h => h.2 hx
    refine ⟨hxb, hb.subset ?_⟩
    apply isPreconnected_connectedComponentIn.m76_subset_of_disjoint_frontier hU
    · rw [hfront]
      apply Set.disjoint_left.mpr
      intro y hy hyC
      exact connectedComponentIn_subset _ _ hyC hy
    · exact ⟨x, mem_connectedComponentIn hxb, hx⟩
  apply Subset.antisymm ?_ hsub
  apply (P.isConnected_inside hP hinj).isPreconnected.m76_subset_of_disjoint_frontier hU
  · rw [hfront]
    exact Set.disjoint_left.mpr (fun _ hx hy => hy.1 hx)
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, hsub hx, hx⟩



theorem closure_inside_eq_of_compact_convex {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {C : Set (ℝ × ℝ)} (hcpt : IsCompact C) (hcv : Convex ℝ C)
    (hne : (interior C).Nonempty) (hfront : frontier C = P.boundary ℝ) :
    closure P.inside = C := by
  have hcl : closure (interior C) = C :=
    (hcv.closure_interior_eq_closure_of_nonempty_interior hne).trans hcpt.isClosed.closure_eq
  have hf : frontier (interior C) = P.boundary ℝ := by
    calc
      frontier (interior C) = C \ interior C := by rw [frontier, interior_interior, hcl]
      _ = frontier C := by rw [frontier, hcpt.isClosed.closure_eq]
      _ = P.boundary ℝ := hfront
  rw [P.inside_eq_of_open_bounded_frontier hP hinj isOpen_interior
    (hcpt.isBounded.subset interior_subset) hne hf]
  exact hcl

end Polygon
