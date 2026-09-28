import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Cap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem isClosed_closed_core_m28 : IsClosed C.closed_core :=
  C.closed_core_compact.isClosed

omit [T2Space M] in
theorem isOpen_core_m28 : IsOpen C.core := by
  rw [C.core_eq_interior_closed_core]
  exact isOpen_interior

omit [T2Space M] in
theorem core_subset_closed_core_m28 : C.core ⊆ C.closed_core := by
  rw [C.core_eq_interior_closed_core]
  exact interior_subset

theorem boundary_eq_closed_core_diff_core_m28 :
    C.boundary_sphere = C.closed_core \ C.core := by
  rw [← C.core_frontier_eq_boundary, frontier, C.isClosed_closed_core_m28.closure_eq,
    C.core_eq_interior_closed_core]

theorem disjoint_core_boundary_m28 : Disjoint C.core C.boundary_sphere := by
  rw [C.boundary_eq_closed_core_diff_core_m28]
  exact disjoint_sdiff_right

omit [T2Space M] in
theorem disjoint_closed_core_end_m28 : Disjoint C.closed_core C.end_neck.carrier := by
  rw [C.closed_core_eq_complement_end]
  exact disjoint_sdiff_left

theorem closed_core_eq_core_union_boundary_m28 :
    C.closed_core = C.core ∪ C.boundary_sphere := by
  rw [C.boundary_eq_closed_core_diff_core_m28,
    union_sdiff_cancel C.core_subset_closed_core_m28]

omit [T2Space M] in
theorem carrier_eq_closed_core_union_end_m28 :
    C.carrier = C.closed_core ∪ C.end_neck.carrier := by
  rw [C.closed_core_eq_complement_end, sdiff_union_of_subset C.end_neck_subset]

theorem subset_core_or_compl_closed_core_m28 {S : Set M} (hS : IsPreconnected S)
    (havoid : Disjoint S C.boundary_sphere) :
    S ⊆ C.core ∨ S ⊆ C.closed_coreᶜ := by
  apply hS.subset_or_subset C.isOpen_core_m28 C.isClosed_closed_core_m28.isOpen_compl
    (disjoint_compl_right.mono_left C.core_subset_closed_core_m28)
  intro x hx
  by_cases hcore : x ∈ C.closed_core
  · left
    by_contra hint
    exact (Set.disjoint_left.mp havoid) hx
      (C.boundary_eq_closed_core_diff_core_m28.symm ▸ ⟨hcore, hint⟩)
  · exact Or.inr hcore

theorem boundary_inter_nonempty_of_crossing_m28 {S : Set M} (hS : IsPreconnected S)
    (hin : (S ∩ C.core).Nonempty) (hout : (S \ C.closed_core).Nonempty) :
    (S ∩ C.boundary_sphere).Nonempty := by
  by_contra h
  have hd : Disjoint S C.boundary_sphere :=
    disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)
  rcases C.subset_core_or_compl_closed_core_m28 hS hd with hside | hside
  · obtain ⟨x, hx, hxout⟩ := hout
    exact hxout (C.core_subset_closed_core_m28 (hside hx))
  · obtain ⟨x, hx, hxin⟩ := hin
    exact hside hx (C.core_subset_closed_core_m28 hxin)

theorem boundary_inter_nonempty_of_core_end_m28 {S : Set M} (hS : IsPreconnected S)
    (hin : (S ∩ C.core).Nonempty) (hout : (S ∩ C.end_neck.carrier).Nonempty) :
    (S ∩ C.boundary_sphere).Nonempty := by
  apply C.boundary_inter_nonempty_of_crossing_m28 hS hin
  obtain ⟨x, hx, hxend⟩ := hout
  exact ⟨x, hx, fun hxcore => Set.disjoint_left.mp C.disjoint_closed_core_end_m28 hxcore hxend⟩

end PoincareConjecture.CapCertificate
