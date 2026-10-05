import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Cap

/-!
# The boundary of a cap core

The compact core and its boundary sphere form a barrier: a connected set
meeting both the core interior and its exterior must meet the boundary.
These statements use the actual closed core in the frozen cap certificate.

Reference: Morgan--Tian, Proposition A.21 and Claims A.23--A.24, pp. 508--514.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem isClosed_closed_core : IsClosed C.closed_core :=
  C.closed_core_compact.isClosed

omit [T2Space M] in
theorem isOpen_core : IsOpen C.core := by
  rw [C.core_eq_interior_closed_core]
  exact isOpen_interior

omit [T2Space M] in
theorem core_subset_closed_core : C.core ⊆ C.closed_core := by
  rw [C.core_eq_interior_closed_core]
  exact interior_subset

omit [T2Space M] in
theorem closed_core_subset_carrier : C.closed_core ⊆ C.carrier := by
  rw [C.closed_core_eq_complement_end]
  exact sdiff_subset

omit [T2Space M] in
theorem core_subset_carrier : C.core ⊆ C.carrier :=
  C.core_subset_closed_core.trans C.closed_core_subset_carrier

theorem boundary_eq_closed_core_diff_core :
    C.boundary_sphere = C.closed_core \ C.core := by
  rw [← C.core_frontier_eq_boundary, frontier, C.isClosed_closed_core.closure_eq,
    C.core_eq_interior_closed_core]

theorem boundary_subset_closed_core : C.boundary_sphere ⊆ C.closed_core := by
  rw [C.boundary_eq_closed_core_diff_core]
  exact sdiff_subset

theorem disjoint_core_boundary : Disjoint C.core C.boundary_sphere := by
  rw [C.boundary_eq_closed_core_diff_core]
  exact disjoint_sdiff_right

omit [T2Space M] in
theorem disjoint_closed_core_end : Disjoint C.closed_core C.end_neck.carrier := by
  rw [C.closed_core_eq_complement_end]
  exact disjoint_sdiff_left

theorem closed_core_eq_core_union_boundary :
    C.closed_core = C.core ∪ C.boundary_sphere := by
  rw [C.boundary_eq_closed_core_diff_core,
    union_sdiff_cancel C.core_subset_closed_core]

omit [T2Space M] in
theorem carrier_eq_closed_core_union_end :
    C.carrier = C.closed_core ∪ C.end_neck.carrier := by
  rw [C.closed_core_eq_complement_end, sdiff_union_of_subset C.end_neck_subset]

/-- A set avoiding the boundary lies on one side of the closed core. -/
theorem subset_core_or_compl_closed_core {S : Set M} (hS : IsPreconnected S)
    (havoid : Disjoint S C.boundary_sphere) :
    S ⊆ C.core ∨ S ⊆ C.closed_coreᶜ := by
  apply hS.subset_or_subset C.isOpen_core C.isClosed_closed_core.isOpen_compl
    (disjoint_compl_right.mono_left C.core_subset_closed_core)
  intro x hx
  by_cases hcore : x ∈ C.closed_core
  · left
    by_contra hint
    exact (Set.disjoint_left.mp havoid) hx
      (C.boundary_eq_closed_core_diff_core.symm ▸ ⟨hcore, hint⟩)
  · exact Or.inr hcore

/-- Every connected crossing from the core to its exterior meets its sphere. -/
theorem boundary_inter_nonempty_of_crossing {S : Set M} (hS : IsPreconnected S)
    (hin : (S ∩ C.core).Nonempty) (hout : (S \ C.closed_core).Nonempty) :
    (S ∩ C.boundary_sphere).Nonempty := by
  by_contra h
  have hd : Disjoint S C.boundary_sphere :=
    disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)
  rcases C.subset_core_or_compl_closed_core hS hd with hside | hside
  · obtain ⟨x, hx, hxout⟩ := hout
    exact hxout (C.core_subset_closed_core (hside hx))
  · obtain ⟨x, hx, hxin⟩ := hin
    exact hside hx (C.core_subset_closed_core hxin)

theorem boundary_inter_nonempty_of_core_end {S : Set M} (hS : IsPreconnected S)
    (hin : (S ∩ C.core).Nonempty) (hout : (S ∩ C.end_neck.carrier).Nonempty) :
    (S ∩ C.boundary_sphere).Nonempty := by
  apply C.boundary_inter_nonempty_of_crossing hS hin
  obtain ⟨x, hx, hxend⟩ := hout
  exact ⟨x, hx, fun hxcore => Set.disjoint_left.mp C.disjoint_closed_core_end hxcore hxend⟩

end PoincareMT.CapCertificate
