import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.CompactNeighborhood
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.InnerAttachment
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}




theorem compact_closure_recut (N : CapCertificate g) {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    IsCompact (closure (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b)) ∧
      closure (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b) ⊆ N.carrier := by
  have heps : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  obtain ⟨W, hW, hYW, _, hWc, hWV⟩ :=
    N.exists_compact_collar_neighborhood (a := 0) (b := 0) (neg_neg_of_pos heps) heps
  have hfront : frontier W ⊆ N.end_neck.carrier := by
    intro x hx
    have hxV := hWV (frontier_subset_closure hx)
    have hxnotW : x ∉ W := (hW.frontier_eq ▸ hx).2
    by_contra hxE
    have hxY : x ∈ N.closed_core := by
      rw [N.closed_core_eq_complement_end]
      exact ⟨hxV, hxE⟩
    exact hxnotW (hYW hxY)
  have hfc : IsCompact (frontier W) :=
    hWc.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hfcont : ContinuousOn (fun x => (N.end_neck.coordinate_inverse x).2)
      (frontier W) :=
    (continuous_snd.comp_continuousOn
      N.end_neck.coordinate_inverse_smooth.continuousOn).mono hfront
  have hflow : ∀ x ∈ frontier W, -N.epsilon⁻¹ <
      (N.end_neck.coordinate_inverse x).2 := by
    intro x hx
    simpa only [N.end_neck_epsilon] using
      (N.end_neck.coordinate_inverse_mem x (hfront hx)).2.1
  obtain ⟨m, hm, hmin⟩ := hfc.exists_forall_le' hfcont hflow
  obtain ⟨c, hc, hcm⟩ := exists_between (lt_min hm hb)
  have hcm' : c < m := hcm.trans_le (min_le_left _ _)
  have hcb : c < b := hcm.trans_le (min_le_right _ _)
  have hconn : IsPreconnected (N.end_neck.region (-N.epsilon⁻¹) c) :=
    N.end_neck.isPreconnected_region (by simp only [N.end_neck_epsilon, le_refl])
      (by simpa only [N.end_neck_epsilon] using (hcb.trans hb').le)
  have hS : N.boundary_neck.center ∈ N.boundary_sphere :=
    N.boundary_eq_neck_sphere.symm ▸ N.boundary_neck.center_on_central_sphere
  obtain ⟨y, hyW, hyR⟩ := mem_closure_iff.mp
    (N.boundary_subset_closure_inner_end hc hS) W hW
    (hYW (N.boundary_subset_closed_core_m28 hS))
  have hinner : N.end_neck.region (-N.epsilon⁻¹) c ⊆ W := by
    apply hconn.subset_of_closure_inter_subset hW ⟨y, hyR, hyW⟩
    intro x hx
    by_contra hxW
    have hxf : x ∈ frontier W := hW.frontier_eq.symm ▸ ⟨hx.1, hxW⟩
    exact (not_lt_of_ge (hmin x hxf)) (hx.2.2.2.trans hcm')
  let T : Set M := N.end_neck.coordinate_map '' (univ ×ˢ Icc c b)
  have hTc : IsCompact T := N.end_neck.isCompact_coordinate_slab_intrinsic
    (by simpa only [N.end_neck_epsilon] using hc)
    (by simpa only [N.end_neck_epsilon] using hb')
  have hTV : T ⊆ N.carrier :=
    (N.end_neck.coordinate_slab_subset_carrier_m28
      (by simpa only [N.end_neck_epsilon] using hc)
      (by simpa only [N.end_neck_epsilon] using hb')).trans N.end_neck_subset
  have hcut : N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b ⊆ closure W ∪ T := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (subset_closure (hYW hx))
    · by_cases hxc : (N.end_neck.coordinate_inverse x).2 < c
      · exact Or.inl (subset_closure (hinner ⟨hx.1, hx.2.1, hxc⟩))
      · exact Or.inr ⟨N.end_neck.coordinate_inverse x,
          ⟨mem_univ _, le_of_not_gt hxc, hx.2.2.le⟩,
          N.end_neck.coordinate_map_coordinate_inverse hx.1⟩
  have hcl := closure_minimal hcut (hWc.union hTc).isClosed
  exact ⟨(hWc.union hTc).of_isClosed_subset isClosed_closure hcl,
    hcl.trans (union_subset hWV hTV)⟩

end PoincareConjecture.CapCertificate
