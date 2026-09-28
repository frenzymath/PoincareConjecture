import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.CoreConnected










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

omit [T2Space M] in
theorem carrier_subset_boundary_component :
    C.carrier ⊆ connectedComponent C.boundary_neck.center := by
  apply C.isConnected_carrier.subset_connectedComponent
  exact C.boundary_neck_subset
    (C.boundary_neck.central_sphere_subset C.boundary_neck.center_on_central_sphere)

theorem core_eq_connectedComponentIn {x : M} (hx : x ∈ C.core) :
    C.core = connectedComponentIn C.boundary_sphereᶜ x := by
  have hc : C.core ⊆ C.boundary_sphereᶜ :=
    Set.disjoint_left.mp C.disjoint_core_boundary
  apply Subset.antisymm
  · exact C.isConnected_core.isPreconnected.subset_connectedComponentIn hx hc
  · have havoid : Disjoint (connectedComponentIn C.boundary_sphereᶜ x)
        C.boundary_sphere := by
      exact disjoint_compl_left.mono_left (connectedComponentIn_subset _ _)
    rcases C.subset_core_or_compl_closed_core isPreconnected_connectedComponentIn havoid with
      h | h
    · exact h
    · exact False.elim (h (mem_connectedComponentIn (hc hx)) (C.core_subset_closed_core hx))

theorem closed_core_eq_closure_connectedComponentIn {x : M} (hx : x ∈ C.core) :
    C.closed_core = closure (connectedComponentIn C.boundary_sphereᶜ x) := by
  rw [← C.core_eq_connectedComponentIn hx, C.closure_core_eq_closed_core]

theorem isConnected_exterior_inter_boundary_neck :
    IsConnected (C.closed_coreᶜ ∩ C.boundary_neck.carrier) := by
  have he : 0 < C.boundary_neck.epsilon⁻¹ := inv_pos.mpr C.boundary_neck.epsilon_pos
  have hdis x (hc : x ∈ C.closed_coreᶜ) (hb : x ∈ C.boundary_neck.central_sphere) : False :=
    hc (C.boundary_subset_closed_core (C.boundary_eq_neck_sphere.symm ▸ hb))
  rcases C.boundary_neck_sides with ⟨hn, hp⟩ | ⟨hp, hn⟩
  · have heq : C.closed_coreᶜ ∩ C.boundary_neck.carrier =
        C.boundary_neck.region 0 C.boundary_neck.epsilon⁻¹ := by
      apply Subset.antisymm
      · rintro x ⟨hc, hx⟩
        rcases C.boundary_neck.carrier_subset_region_union_central_union_region hx with
          (hneg | hsphere) | hpos
        · exact (hc (C.core_subset_closed_core (hn hneg))).elim
        · exact (hdis x hc hsphere).elim
        · exact hpos
      · intro x hx
        exact ⟨fun hc => Set.disjoint_left.mp C.disjoint_closed_core_end hc (hp hx), hx.1⟩
    rw [heq]
    exact C.boundary_neck.isConnected_region (neg_nonpos.mpr he.le) le_rfl he
  · have heq : C.closed_coreᶜ ∩ C.boundary_neck.carrier =
        C.boundary_neck.region (-C.boundary_neck.epsilon⁻¹) 0 := by
      apply Subset.antisymm
      · rintro x ⟨hc, hx⟩
        rcases C.boundary_neck.carrier_subset_region_union_central_union_region hx with
          (hneg | hsphere) | hpos
        · exact hneg
        · exact (hdis x hc hsphere).elim
        · exact (hc (C.core_subset_closed_core (hp hpos))).elim
      · intro x hx
        exact ⟨fun hc => Set.disjoint_left.mp C.disjoint_closed_core_end hc (hn hx), hx.1⟩
    rw [heq]
    exact C.boundary_neck.isConnected_region le_rfl he.le (neg_lt_zero.mpr he)

theorem isConnected_component_diff_closed_core :
    IsConnected (connectedComponent C.boundary_neck.center \ C.closed_core) := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let V := connectedComponent C.boundary_neck.center
  have hV : IsOpen V := isOpen_connectedComponent
  let : LocallyConnectedSpace V := hV.locallyConnectedSpace
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let A : Set V := Subtype.val ⁻¹' C.closed_coreᶜ
  let U : Set V := Subtype.val ⁻¹' C.boundary_neck.carrier
  have hA : IsOpen A := C.isClosed_closed_core.isOpen_compl.preimage continuous_subtype_val
  have hU : IsOpen U := C.boundary_neck.carrier_open.preimage continuous_subtype_val
  have hImage : Subtype.val '' (A ∩ U) = C.closed_coreᶜ ∩ C.boundary_neck.carrier := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, C.boundary_neck.carrier_subset_connectedComponent hx.2⟩, hx, rfl⟩
  have hAU : IsConnected (A ∩ U) := by
    refine ⟨?_, ?_⟩
    · have hn := C.isConnected_exterior_inter_boundary_neck.nonempty
      rw [← hImage] at hn
      exact hn.of_image
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hImage]
      exact C.isConnected_exterior_inter_boundary_neck.isPreconnected
  have hfront : frontier A ⊆ U := by
    intro x hx
    have hb : x.val ∈ C.boundary_sphere := by
      rw [← C.core_frontier_eq_boundary, ← frontier_compl]
      exact continuous_subtype_val.frontier_preimage_subset C.closed_coreᶜ hx
    exact C.boundary_neck.central_sphere_subset (C.boundary_eq_neck_sphere ▸ hb)
  have hne : A ≠ univ := by
    intro h
    obtain ⟨x, hx⟩ := C.core_nonempty
    let y : V := ⟨x, C.carrier_subset_boundary_component (C.core_subset_carrier hx)⟩
    have hy : y ∈ A := h ▸ mem_univ y
    exact hy (C.core_subset_closed_core hx)
  have hconn := Poincare.Topology.isConnected_of_inter_of_frontier_subset hA hU hAU hfront hne
  have hImageA : Subtype.val '' A = V \ C.closed_core := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [← hImageA]
  exact hconn.image _ continuous_subtype_val.continuousOn

theorem isOpen_component_diff_closed_core :
    IsOpen (connectedComponent C.boundary_neck.center \ C.closed_core) := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  exact isOpen_connectedComponent.sdiff C.isClosed_closed_core

theorem core_union_exterior :
    C.core ∪ (connectedComponent C.boundary_neck.center \ C.closed_core) =
      connectedComponent C.boundary_neck.center \ C.boundary_sphere := by
  ext x
  rw [C.boundary_eq_closed_core_diff_core]
  have hc : x ∈ C.core → x ∈ connectedComponent C.boundary_neck.center :=
    fun hx => C.carrier_subset_boundary_component (C.core_subset_carrier hx)
  have hk := C.core_subset_closed_core (a := x)
  simp only [mem_union, mem_sdiff]
  tauto

theorem exterior_eq_connectedComponentIn {x : M}
    (hx : x ∈ connectedComponent C.boundary_neck.center \ C.closed_core) :
    connectedComponent C.boundary_neck.center \ C.closed_core =
      connectedComponentIn C.boundary_sphereᶜ x := by
  have hexterior : connectedComponent C.boundary_neck.center \ C.closed_core ⊆
      C.boundary_sphereᶜ := by
    intro y hy hb
    exact hy.2 (C.boundary_subset_closed_core hb)
  apply Subset.antisymm
  · exact C.isConnected_component_diff_closed_core.isPreconnected.subset_connectedComponentIn
      hx hexterior
  · have hcomponent : connectedComponentIn C.boundary_sphereᶜ x ⊆
        connectedComponent C.boundary_neck.center := by
      have hs := isPreconnected_connectedComponentIn.subset_connectedComponent
        (mem_connectedComponentIn (hexterior hx))
      rwa [← connectedComponent_eq hx.1] at hs
    have havoid : Disjoint (connectedComponentIn C.boundary_sphereᶜ x)
        C.boundary_sphere :=
      disjoint_compl_left.mono_left (connectedComponentIn_subset _ _)
    rcases C.subset_core_or_compl_closed_core isPreconnected_connectedComponentIn havoid with
      h | h
    · exact False.elim (hx.2 (C.core_subset_closed_core
        (h (mem_connectedComponentIn (hexterior hx)))))
    · exact fun y hy => ⟨hcomponent hy, h hy⟩

theorem frontier_exterior_eq_boundary :
    frontier (connectedComponent C.boundary_neck.center \ C.closed_core) =
      C.boundary_sphere := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  apply Subset.antisymm
  · have hcc : IsClopen (connectedComponent C.boundary_neck.center) :=
      ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
    intro x hx
    rcases frontier_inter_subset (connectedComponent C.boundary_neck.center) C.closed_coreᶜ hx
      with h | h
    · exact (hcc.frontier_eq ▸ h.1).elim
    · simpa only [frontier_compl, C.core_frontier_eq_boundary] using h.2
  · intro x hx
    refine ⟨?_, ?_⟩
    · apply closure_mono (show C.end_neck.carrier ⊆
          connectedComponent C.boundary_neck.center \ C.closed_core from ?_)
        (C.boundary_subset_closure_end hx)
      intro y hy
      exact ⟨C.carrier_subset_boundary_component (C.end_neck_subset hy),
        fun hk => Set.disjoint_left.mp C.disjoint_closed_core_end hk hy⟩
    · exact fun hi => (interior_subset hi).2 (C.boundary_subset_closed_core hx)

theorem closed_core_union_closure_exterior :
    C.closed_core ∪ closure (connectedComponent C.boundary_neck.center \ C.closed_core) =
      connectedComponent C.boundary_neck.center := by
  have hK := C.closed_core_subset_carrier.trans C.carrier_subset_boundary_component
  apply Subset.antisymm
  · exact union_subset hK (closure_minimal sdiff_subset isClosed_connectedComponent)
  · intro x hx
    by_cases hk : x ∈ C.closed_core
    · exact Or.inl hk
    · exact Or.inr (subset_closure ⟨hx, hk⟩)

end PoincareConjecture.CapCertificate
