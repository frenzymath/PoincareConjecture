import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Connected










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem isConnected_core_inter_boundary_neck :
    IsConnected (C.core ∩ C.boundary_neck.carrier) := by
  have he : 0 < C.boundary_neck.epsilon⁻¹ := inv_pos.mpr C.boundary_neck.epsilon_pos
  have hdis x (hc : x ∈ C.core) (hend : x ∈ C.end_neck.carrier) : False :=
    Set.disjoint_left.mp C.disjoint_closed_core_end (C.core_subset_closed_core hc) hend
  have hbdis x (hc : x ∈ C.core) (hb : x ∈ C.boundary_neck.central_sphere) : False :=
    Set.disjoint_left.mp C.disjoint_core_boundary hc (C.boundary_eq_neck_sphere.symm ▸ hb)
  rcases C.boundary_neck_sides with ⟨hn, hp⟩ | ⟨hp, hn⟩
  · have hEq : C.core ∩ C.boundary_neck.carrier =
        C.boundary_neck.region (-C.boundary_neck.epsilon⁻¹) 0 := by
      apply Subset.antisymm
      · rintro x ⟨hc, hx⟩
        rcases C.boundary_neck.carrier_subset_region_union_central_union_region hx with
          (hneg | hsphere) | hpos
        · exact hneg
        · exact (hbdis x hc hsphere).elim
        · exact (hdis x hc (hp hpos)).elim
      · intro x hx
        exact ⟨hn hx, hx.1⟩
    rw [hEq]
    exact C.boundary_neck.isConnected_region le_rfl he.le (neg_lt_zero.mpr he)
  · have hEq : C.core ∩ C.boundary_neck.carrier =
        C.boundary_neck.region 0 C.boundary_neck.epsilon⁻¹ := by
      apply Subset.antisymm
      · rintro x ⟨hc, hx⟩
        rcases C.boundary_neck.carrier_subset_region_union_central_union_region hx with
          (hneg | hsphere) | hpos
        · exact (hdis x hc (hn hneg)).elim
        · exact (hbdis x hc hsphere).elim
        · exact hpos
      · intro x hx
        exact ⟨hp hx, hx.1⟩
    rw [hEq]
    exact C.boundary_neck.isConnected_region (neg_nonpos.mpr he.le) le_rfl he

theorem isConnected_core : IsConnected C.core := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : LocallyConnectedSpace C.carrier := C.carrier_open.locallyConnectedSpace
  let : ConnectedSpace C.carrier := isConnected_iff_connectedSpace.mp C.isConnected_carrier
  let A : Set C.carrier := Subtype.val ⁻¹' C.core
  let U : Set C.carrier := Subtype.val ⁻¹' C.boundary_neck.carrier
  have hA : IsOpen A := C.isOpen_core.preimage continuous_subtype_val
  have hU : IsOpen U := C.boundary_neck.carrier_open.preimage continuous_subtype_val
  have hImage : Subtype.val '' (A ∩ U) = C.core ∩ C.boundary_neck.carrier := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, C.core_subset_carrier hx.1⟩, hx, rfl⟩
  have hAU : IsConnected (A ∩ U) := by
    refine ⟨?_, ?_⟩
    · have hn := C.isConnected_core_inter_boundary_neck.nonempty
      rw [← hImage] at hn
      exact hn.of_image
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hImage]
      exact C.isConnected_core_inter_boundary_neck.isPreconnected
  have hfront : frontier A ⊆ U := by
    intro x hx
    have hb : x.val ∈ C.boundary_sphere := by
      rw [← C.frontier_core_eq_boundary]
      exact continuous_subtype_val.frontier_preimage_subset C.core hx
    exact C.boundary_neck.central_sphere_subset (C.boundary_eq_neck_sphere ▸ hb)
  have hne : A ≠ univ := by
    intro h
    have hend := C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere
    let x : C.carrier := ⟨C.end_neck.center, C.end_neck_subset hend⟩
    have hx : x ∈ A := h ▸ mem_univ x
    exact Set.disjoint_left.mp C.disjoint_closed_core_end (C.core_subset_closed_core hx) hend
  have hconn := Poincare.Topology.isConnected_of_inter_of_frontier_subset hA hU hAU hfront hne
  have hImageA : Subtype.val '' A = C.core := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, C.core_subset_carrier hx⟩, hx, rfl⟩
  rw [← hImageA]
  exact hconn.image _ continuous_subtype_val.continuousOn

theorem isConnected_closed_core : IsConnected C.closed_core := by
  rw [← C.closure_core_eq_closed_core]
  exact C.isConnected_core.closure

end PoincareConjecture.CapCertificate
