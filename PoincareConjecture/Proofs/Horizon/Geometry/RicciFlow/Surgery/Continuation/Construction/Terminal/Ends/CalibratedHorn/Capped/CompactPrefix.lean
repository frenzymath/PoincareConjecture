import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Ends
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Regions
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)


theorem boundary_subset_closure_negative_region {a : ℝ}
    (ha : -C.epsilon⁻¹ < a) :
    C.boundary_sphere ⊆ closure (C.end_neck.region (-C.epsilon⁻¹) a) := by
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  intro x hx
  by_cases hhalf : -C.epsilon⁻¹ / 2 ≤ a
  · have hsub : C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆
        C.end_neck.region (-C.epsilon⁻¹) a :=
      fun y hy => ⟨hy.1, hy.2.1, hy.2.2.trans_le hhalf⟩
    exact closure_mono hsub (C.boundary_subset_negative_end_closure hx)
  · let K := C.end_neck.coordinate_map '' (univ ×ˢ Icc a (-C.epsilon⁻¹ / 2))
    have hK : IsCompact K := C.end_neck.isCompact_coordinate_slab
      (by simpa only [C.end_neck_epsilon] using ha)
      (by rw [C.end_neck_epsilon]; linarith)
    have hKend : K ⊆ C.end_neck.carrier :=
      C.end_neck.coordinate_slab_subset_carrier
        (by simpa only [C.end_neck_epsilon] using ha)
        (by rw [C.end_neck_epsilon]; linarith)
    have hsub : C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆
        C.end_neck.region (-C.epsilon⁻¹) a ∪ K := by
      intro y hy
      by_cases hya : (C.end_neck.coordinate_inverse y).2 < a
      · exact Or.inl ⟨hy.1, hy.2.1, hya⟩
      · exact Or.inr ⟨C.end_neck.coordinate_inverse y,
          ⟨mem_univ _, le_of_not_gt hya, hy.2.2.le⟩,
          C.end_neck.coordinate_map_coordinate_inverse hy.1⟩
    have h := closure_mono hsub (C.boundary_subset_negative_end_closure hx)
    rw [closure_union, hK.isClosed.closure_eq] at h
    exact h.resolve_right fun hxK => disjoint_left.mp C.disjoint_closed_core_end
      (C.boundary_subset_closed_core hx) (hKend hxK)


theorem exists_compact_negative_region :
    ∃ a ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
      IsCompact (closure (C.end_neck.region (-C.epsilon⁻¹) a)) ∧
      closure (C.end_neck.region (-C.epsilon⁻¹) a) ⊆ C.carrier := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨K, hK, hcore, hKC⟩ := exists_compact_between C.closed_core_compact
    C.carrier_open C.closed_core_subset_carrier
  have hfront : frontier K ⊆ C.end_neck.carrier := by
    intro x hx
    have hxC := hKC (hK.isClosed.frontier_subset hx)
    rcases C.carrier_eq_closed_core_union_end ▸ hxC with hxcore | hxend
    · exact False.elim (hx.2 (hcore hxcore))
    · exact hxend
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hchoose : ∃ a ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
      Disjoint (C.end_neck.region (-C.epsilon⁻¹) a) (frontier K) := by
    by_cases hne : (frontier K).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (hK.of_isClosed_subset isClosed_frontier
        hK.isClosed.frontier_subset).exists_isMinOn hne
          (C.end_neck.coordinate_inverse_smooth.continuousOn.snd.mono hfront)
      have hxlo := (C.end_neck.coordinate_inverse_mem x (hfront hx)).2.1
      rw [C.end_neck_epsilon] at hxlo
      obtain ⟨a, ha, ha'⟩ := exists_between (lt_min hxlo (neg_lt_self hR))
      refine ⟨a, ⟨ha, ha'.trans_le (min_le_right _ _)⟩,
        disjoint_left.mpr ?_⟩
      intro y hy hyK
      exact (not_lt_of_ge (hmin hyK))
        (hy.2.2.trans (ha'.trans_le (min_le_left _ _)))
    · exact ⟨0, ⟨neg_lt_zero.mpr hR, hR⟩, by
        rw [not_nonempty_iff_eq_empty.mp hne]; exact disjoint_empty _⟩
  obtain ⟨a, ha, havoid⟩ := hchoose
  have hb : C.boundary_neck.center ∈ C.boundary_sphere :=
    C.boundary_eq_neck_sphere.symm ▸ C.boundary_neck.center_on_central_sphere
  obtain ⟨x, hxK, hxend⟩ := mem_closure_iff_nhds.mp
    (C.boundary_subset_closure_negative_region ha.1 hb) _
      (isOpen_interior.mem_nhds (hcore (C.boundary_subset_closed_core hb)))
  have hsub : C.end_neck.region (-C.epsilon⁻¹) a ⊆ interior K :=
    Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      (C.end_neck.isConnected_region (by rw [C.end_neck_epsilon])
        (by simpa only [C.end_neck_epsilon] using ha.2.le) ha.1).isPreconnected
      havoid ⟨x, hxend, hxK⟩
  have hclosure := closure_minimal (hsub.trans interior_subset) hK.isClosed
  exact ⟨a, ha, hK.of_isClosed_subset isClosed_closure hclosure,
    hclosure.trans hKC⟩


theorem isCompact_truncated_core {b : ℝ} (hb : b < C.epsilon⁻¹) :
    IsCompact (C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) b)) ∧
      C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) b) ⊆ C.carrier := by
  obtain ⟨a, ha, hnegative, hnegativeC⟩ := C.exists_compact_negative_region
  let K := C.end_neck.coordinate_map '' (univ ×ˢ Icc a (max a b))
  have hlo : -C.end_neck.epsilon⁻¹ < a := by
    simpa only [C.end_neck_epsilon] using ha.1
  have hhi : max a b < C.end_neck.epsilon⁻¹ := by
    simpa only [C.end_neck_epsilon] using max_lt ha.2 hb
  have hK : IsCompact K := C.end_neck.isCompact_coordinate_slab hlo hhi
  have hKC : K ⊆ C.carrier :=
    (C.end_neck.coordinate_slab_subset_carrier hlo hhi).trans C.end_neck_subset
  have hsub : C.end_neck.region (-C.epsilon⁻¹) b ⊆
      C.end_neck.region (-C.epsilon⁻¹) a ∪ K := by
    intro x hx
    by_cases hxa : (C.end_neck.coordinate_inverse x).2 < a
    · exact Or.inl ⟨hx.1, hx.2.1, hxa⟩
    · exact Or.inr ⟨C.end_neck.coordinate_inverse x,
        ⟨mem_univ _, le_of_not_gt hxa, hx.2.2.le.trans (le_max_right _ _)⟩,
        C.end_neck.coordinate_map_coordinate_inverse hx.1⟩
  have hclosure : closure (C.end_neck.region (-C.epsilon⁻¹) b) ⊆
      closure (C.end_neck.region (-C.epsilon⁻¹) a) ∪ K := by
    simpa only [closure_union, hK.isClosed.closure_eq] using closure_mono hsub
  exact ⟨C.closed_core_compact.union
      ((hnegative.union hK).of_isClosed_subset isClosed_closure hclosure),
    union_subset C.closed_core_subset_carrier
      (hclosure.trans (union_subset hnegativeC hKC))⟩

end PoincareConjecture.CapCertificate
