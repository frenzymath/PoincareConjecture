import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CoreComponents
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Neck.NeckCoordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryEndCut

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {N P : EpsilonNeck g} (C : SurgeryEndCut N)

theorem tail_isOpen : IsOpen C.tail := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  rw [C.component_eq]
  exact N.isCompact_central_sphere.isClosed.isOpen_compl.connectedComponentIn

theorem tail_disjoint_central : Disjoint C.tail N.central_sphere := by
  apply disjoint_left.mpr
  intro x hx
  rw [C.component_eq] at hx
  exact connectedComponentIn_subset _ _ hx

theorem closure_tail : closure C.tail = C.tail ∪ N.central_sphere := by
  rw [closure_eq_self_union_frontier, C.frontier_eq]

theorem carrier_inter_tail : N.carrier ∩ C.tail = N.region 0 N.epsilon⁻¹ := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨hx.1, ?_, (N.coordinate_inverse_mem x hx.1).2.2⟩
    apply lt_of_not_ge
    intro hnonpos
    rcases (MetricSurgery.neck_retained_iff N).mpr ⟨hx.1, hnonpos⟩ with hn | hc
    · exact disjoint_left.mp C.negative_disjoint hn hx.2
    · exact disjoint_left.mp C.tail_disjoint_central hx.2 hc
  · exact fun x hx => ⟨hx.1, C.positive_subset hx⟩

theorem negative_disjoint_closure :
    Disjoint (N.region (-N.epsilon⁻¹) 0) (closure C.tail) :=
  C.negative_disjoint.closure_right (MetricSurgery.neck_region_isOpen _ _ _)

theorem carrier_diff_closure_tail :
    N.carrier \ closure C.tail = N.region (-N.epsilon⁻¹) 0 := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨hx.1, (N.coordinate_inverse_mem x hx.1).2.1, ?_⟩
    apply lt_of_not_ge
    intro hnonneg
    rcases hnonneg.eq_or_lt with hz | hz
    · exact hx.2 (frontier_subset_closure (C.frontier_eq.symm ▸
        (MetricSurgery.neck_central_iff N).mpr ⟨hx.1, hz.symm⟩))
    · exact hx.2 (subset_closure (C.positive_subset
        ⟨hx.1, hz, (N.coordinate_inverse_mem x hx.1).2.2⟩))
  · exact fun x hx => ⟨hx.1, disjoint_left.mp C.negative_disjoint_closure hx⟩

theorem carrier_disjoint_other_closure (D : SurgeryEndCut P)
    (hneck : Disjoint N.carrier P.carrier) (htail : Disjoint C.tail D.tail) :
    Disjoint N.carrier (closure D.tail) := by
  have hfront : Disjoint N.carrier (frontier D.tail) := by
    rw [D.frontier_eq]
    exact hneck.mono_right P.central_sphere_subset
  have hcenter : N.center ∉ closure D.tail := by
    rw [D.closure_tail]
    rintro (ht | hs)
    · exact disjoint_left.mp (htail.closure_left D.tail_isOpen)
        (frontier_subset_closure (C.frontier_eq.symm ▸ N.center_on_central_sphere)) ht
    · exact disjoint_left.mp hneck
        (N.central_sphere_subset N.center_on_central_sphere) (P.central_sphere_subset hs)
  have hsub : N.carrier ⊆ D.tail ∪ (closure D.tail)ᶜ := by
    intro x hx
    by_cases ht : x ∈ D.tail
    · exact Or.inl ht
    · exact Or.inr (fun hc => disjoint_left.mp hfront hx
        ⟨hc, fun hi => ht (interior_subset hi)⟩)
  rcases N.isConnected_carrier.isPreconnected.subset_or_subset
      D.tail_isOpen isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hsub with h | h
  · exact False.elim (hcenter (subset_closure
      (h (N.central_sphere_subset N.center_on_central_sphere))))
  · exact disjoint_left.mpr fun _ hx => h hx

end PoincareConjecture.SurgeryEndCut
