import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRecutOpen
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)




theorem recutCarrier_compact_closure {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    IsCompact (closure (N.recutCarrier b)) ∧
      closure (N.recutCarrier b) ⊆ N.carrier := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨W, hW, hYW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure
    N.closed_core_compact N.carrier_open N.closed_core_subset_carrier
  have hfront : frontier W ⊆ N.end_neck.carrier := by
    intro x hx
    by_contra he
    have hy : x ∈ N.closed_core := by
      rw [N.closed_core_eq_complement_end]
      exact ⟨hWV hx.1, he⟩
    exact hx.2 (hW.interior_eq.symm ▸ hYW hy)
  have hfc : IsCompact (frontier W) :=
    hWc.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨d, hd, hdbound⟩ := hfc.exists_forall_le'
    (N.end_neck.coordinate_inverse_smooth.continuousOn.snd.mono hfront)
    (a := -N.epsilon⁻¹) (by
      intro x hx
      have ht := (N.end_neck.coordinate_inverse_mem x (hfront hx)).2.1
      simpa only [N.end_neck_epsilon] using ht)
  let c := min ((-N.epsilon⁻¹ + b) / 2) ((-N.epsilon⁻¹ + d) / 2)
  have hc : -N.epsilon⁻¹ < c := by
    apply lt_min <;> linarith
  have hcb : c < b := (min_le_left _ _).trans_lt (by linarith)
  have hcd : c < d := (min_le_right _ _).trans_lt (by linarith)
  have hSc : IsPreconnected (N.end_neck.region (-N.epsilon⁻¹) c) := by
    apply N.end_neck.region_isPreconnected
    · rw [N.end_neck_epsilon]
    · rw [N.end_neck_epsilon]
      exact (hcb.trans hb').le
  have hcenter : N.boundary_neck.center ∈ N.boundary_sphere :=
    N.boundary_eq_neck_sphere.symm ▸ N.boundary_neck.center_on_central_sphere
  obtain ⟨y, hyW, hyS⟩ := mem_closure_iff.mp
    (N.boundary_subset_inner_end_closure hc hcenter) W hW
    (hYW (N.boundary_subset_closed_core hcenter))
  have hSW : N.end_neck.region (-N.epsilon⁻¹) c ⊆ W := by
    apply hSc.subset_of_closure_inter_subset hW ⟨y, hyS, hyW⟩
    intro x hx
    by_contra hxW
    have hxF : x ∈ frontier W := ⟨hx.1, by simpa only [hW.interior_eq] using hxW⟩
    exact (not_lt_of_ge (hdbound x hxF)) (hx.2.2.2.trans hcd)
  let K := N.end_neck.coordinate_map '' (univ ×ˢ Icc c b)
  have hK : IsCompact K := N.end_neck.isCompact_image_closed_axial_interval
    (by simpa only [N.end_neck_epsilon] using hc)
    (by simpa only [N.end_neck_epsilon] using hb')
  have hKV : K ⊆ N.carrier :=
    (N.end_neck.image_closed_axial_interval_subset_carrier
      (by simpa only [N.end_neck_epsilon] using hc)
      (by simpa only [N.end_neck_epsilon] using hb')).trans N.end_neck_subset
  have hsplit : N.recutCarrier b ⊆ W ∪ K := by
    intro x hx
    rcases hx with hxY | hxE
    · exact Or.inl (hYW hxY)
    · by_cases hxc : (N.end_neck.coordinate_inverse x).2 < c
      · exact Or.inl (hSW ⟨hxE.1, hxE.2.1, hxc⟩)
      · exact Or.inr ⟨N.end_neck.coordinate_inverse x,
          ⟨mem_univ _, le_of_not_gt hxc, hxE.2.2.le⟩,
          N.end_neck.coordinate_map_coordinate_inverse hxE.1⟩
  have hcl : closure (N.recutCarrier b) ⊆ closure W ∪ K := by
    simpa only [closure_union, hK.isClosed.closure_eq] using closure_mono hsplit
  exact ⟨(hWc.union hK).of_isClosed_subset isClosed_closure hcl,
    hcl.trans (union_subset hWV hKV)⟩

end PoincareConjecture.CapCertificate
