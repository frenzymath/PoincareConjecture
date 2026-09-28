import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Cap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace M38Schoenflies

open _root_.PoincareConjecture

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

omit [T2Space M] in
theorem core_subset_carrier : C.core ⊆ C.carrier := C.core_subset_carrier'

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

theorem boundary_eq_closed_core_diff_core :
    C.boundary_sphere = C.closed_core \ C.core := by
  rw [← C.core_frontier_eq_boundary, frontier, (isClosed_closed_core C).closure_eq,
    C.core_eq_interior_closed_core]

theorem disjoint_core_boundary : Disjoint C.core C.boundary_sphere := by
  rw [boundary_eq_closed_core_diff_core C]
  exact disjoint_sdiff_right

omit [T2Space M] in
theorem disjoint_closed_core_end : Disjoint C.closed_core C.end_neck.carrier := by
  rw [C.closed_core_eq_complement_end]
  exact disjoint_sdiff_left

theorem closed_core_eq_core_union_boundary :
    C.closed_core = C.core ∪ C.boundary_sphere := by
  rw [boundary_eq_closed_core_diff_core C,
    union_sdiff_cancel (core_subset_closed_core C)]

omit [T2Space M] in
theorem carrier_eq_closed_core_union_end :
    C.carrier = C.closed_core ∪ C.end_neck.carrier := by
  rw [C.closed_core_eq_complement_end, sdiff_union_of_subset C.end_neck_subset]

theorem subset_core_or_compl_closed_core {S : Set M} (hS : IsPreconnected S)
    (havoid : Disjoint S C.boundary_sphere) :
    S ⊆ C.core ∨ S ⊆ C.closed_coreᶜ := by
  apply hS.subset_or_subset (isOpen_core C) (isClosed_closed_core C).isOpen_compl
    (disjoint_compl_right.mono_left (core_subset_closed_core C))
  intro x hx
  by_cases hcore : x ∈ C.closed_core
  · left
    by_contra hint
    exact (Set.disjoint_left.mp havoid) hx
      ((boundary_eq_closed_core_diff_core C).symm ▸ ⟨hcore, hint⟩)
  · exact Or.inr hcore

theorem boundary_inter_nonempty_of_crossing {S : Set M} (hS : IsPreconnected S)
    (hin : (S ∩ C.core).Nonempty) (hout : (S \ C.closed_core).Nonempty) :
    (S ∩ C.boundary_sphere).Nonempty := by
  by_contra h
  have hd : Disjoint S C.boundary_sphere :=
    disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)
  rcases subset_core_or_compl_closed_core C hS hd with hside | hside
  · obtain ⟨x, hx, hxout⟩ := hout
    exact hxout (core_subset_closed_core C (hside hx))
  · obtain ⟨x, hx, hxin⟩ := hin
    exact hside hx (core_subset_closed_core C hxin)

theorem boundary_inter_nonempty_of_core_end {S : Set M} (hS : IsPreconnected S)
    (hin : (S ∩ C.core).Nonempty) (hout : (S ∩ C.end_neck.carrier).Nonempty) :
    (S ∩ C.boundary_sphere).Nonempty := by
  apply boundary_inter_nonempty_of_crossing C hS hin
  obtain ⟨x, hx, hxend⟩ := hout
  exact ⟨x, hx, fun hxcore => Set.disjoint_left.mp (disjoint_closed_core_end C) hxcore hxend⟩

end PoincareConjecture.CapCertificate
end M38Schoenflies
