import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.EnclosingRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

private theorem subset_open_of_disjoint_frontier {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hS : IsConnected S) (hU : IsOpen U)
    (hmeet : (U ∩ S).Nonempty) (hdis : Disjoint S (frontier U)) : S ⊆ U := by
  rw [← hU.interior_eq]
  apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    hS.isPreconnected hdis
  rwa [hU.interior_eq, inter_comm]

theorem exists_finite_chain_closed_side_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T → ∀ b : ℤ, T.shape = .finite 0 b →
          ∀ (D : CapCertificate g) (e : M ≃ₜ M),
            e '' D.boundary_sphere ⊆ C.carrier ∪ (T.unionOpen : Set M) →
            e '' D.closed_core ⊆ C.carrier ∪ (T.unionOpen : Set M) ∨
              (IsCompact (e '' closure (connectedComponent D.boundary_neck.center \
                  D.closed_core)) ∧
                e '' closure (connectedComponent D.boundary_neck.center \ D.closed_core) ⊆
                  C.carrier ∪ (T.unionOpen : Set M)) := by
  obtain ⟨ε₀, hε₀, hsmall, henclose⟩ := exists_finite_chain_enclosing_region_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε H T hT b hshape D e hboundary
  have hDs : IsCompact D.boundary_sphere := D.closed_core_compact.of_isClosed_subset
    (D.core_frontier_eq_boundary ▸ isClosed_frontier) D.boundary_subset_closed_core
  obtain ⟨U, hU, hcompact, hUA, hDU, hconn⟩ :=
    henclose C hε H T hT b hshape (hDs.image e.continuous) hboundary
  let V := e.symm '' U
  have hV : IsOpen V := e.symm.isOpenMap U hU
  have hVcompact : IsCompact (closure V) := by
    rw [← e.symm.image_closure]
    exact hcompact.image e.symm.continuous
  have hVA : e '' closure V ⊆ C.carrier ∪ (T.unionOpen : Set M) := by
    rw [← e.symm.image_closure]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa only [e.apply_symm_apply] using hUA hy
  have hDV : D.boundary_sphere ⊆ V := fun x hx =>
    ⟨e x, hDU (mem_image_of_mem e hx), e.symm_apply_apply x⟩
  have hVconn : IsConnected (frontier V) := by
    rw [← e.symm.image_frontier]
    exact hconn.image e.symm e.symm.continuous.continuousOn
  have hdis : Disjoint (frontier V) D.boundary_sphere :=
    disjoint_left.mpr (fun x hx hxD => hx.2 (hV.interior_eq.symm ▸ hDV hxD))
  have hp : D.boundary_neck.center ∈ D.boundary_sphere :=
    D.boundary_eq_neck_sphere.symm ▸ D.boundary_neck.center_on_central_sphere
  have hcoremeet : (V ∩ D.core).Nonempty :=
    mem_closure_iff.mp (D.closure_core_eq_closed_core.symm ▸ D.boundary_subset_closed_core hp)
      V hV (hDV hp)
  have hextmeet : (V ∩ (connectedComponent D.boundary_neck.center \ D.closed_core)).Nonempty :=
    mem_closure_iff.mp ((D.frontier_exterior_eq_boundary.symm ▸ hp).1) V hV (hDV hp)
  rcases D.subset_core_or_compl_closed_core hVconn.isPreconnected hdis with hcore | hext
  · right
    have hsub : connectedComponent D.boundary_neck.center \ D.closed_core ⊆ V := by
      apply subset_open_of_disjoint_frontier D.isConnected_component_diff_closed_core hV hextmeet
      exact disjoint_left.mpr (fun x hx hxF => hx.2 (D.core_subset_closed_core (hcore hxF)))
    have hcl := closure_mono hsub
    exact ⟨(hVcompact.of_isClosed_subset isClosed_closure hcl).image e.continuous,
      (image_mono hcl).trans hVA⟩
  · left
    have hsub : D.core ⊆ V := by
      apply subset_open_of_disjoint_frontier D.isConnected_core hV hcoremeet
      exact disjoint_left.mpr (fun x hx hxF => hext hxF (D.core_subset_closed_core hx))
    rw [← D.closure_core_eq_closed_core]
    exact (image_mono (closure_mono hsub)).trans hVA

theorem exists_finite_chain_transported_boundary_closing_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T → ∀ b : ℤ, T.shape = .finite 0 b →
          ∀ (D : CapCertificate g) (e : M ≃ₜ M),
            e '' D.boundary_sphere ⊆ C.carrier ∪ (T.unionOpen : Set M) →
            e '' D.carrier = D.carrier →
            (frontier (C.carrier ∪ (T.unionOpen : Set M)) ∩ (e '' D.closed_core)).Nonempty →
            C.carrier ∪ (T.unionOpen : Set M) ∪ D.carrier =
                connectedComponent C.boundary_neck.center ∧
              IsCompact (C.carrier ∪ (T.unionOpen : Set M) ∪ D.carrier) := by
  obtain ⟨ε₀, hε₀, hsmall, hside⟩ := exists_finite_chain_closed_side_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε H T hT b hshape D e hboundary hcarrier hcontact
  let A := C.carrier ∪ (T.unionOpen : Set M)
  have hA : IsOpen A := C.carrier_open.union T.unionOpen.isOpen
  have hcenter : C.end_neck.center ∈ C.end_neck.carrier :=
    C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere
  have hmeet : (C.carrier ∩ (T.unionOpen : Set M)).Nonempty :=
    ⟨C.end_neck.center, C.end_neck_subset hcenter,
      mem_iUnion.mpr ⟨⟨0, hT.zero_active⟩, hT.first_neck.symm ▸ hcenter⟩⟩
  have hconn : IsConnected A := C.isConnected_carrier.union hmeet T.isConnected_union
  have hAcomp : A ⊆ connectedComponent C.boundary_neck.center :=
    hconn.subset_connectedComponent (Or.inl (C.boundary_neck_subset
      (C.boundary_neck.central_sphere_subset C.boundary_neck.center_on_central_sphere)))
  rcases hside C hε H T hT b hshape D e hboundary with hinside | ⟨hc, houtside⟩
  · obtain ⟨x, hx, hxD⟩ := hcontact
    exact False.elim ((hA.frontier_eq ▸ hx).2 (hinside hxD))
  · have hcenterD : e D.boundary_neck.center ∈ A := by
      apply hboundary
      apply mem_image_of_mem
      rw [D.boundary_eq_neck_sphere]
      exact D.boundary_neck.center_on_central_sphere
    have hcomponent : e '' connectedComponent D.boundary_neck.center =
        connectedComponent C.boundary_neck.center := by
      have h := e.image_connectedComponentIn (s := univ)
        (x := D.boundary_neck.center) (mem_univ _)
      simp only [image_univ, e.surjective.range_eq, connectedComponentIn_univ] at h
      exact h.trans (connectedComponent_eq (hAcomp hcenterD)).symm
    have hclosed : e '' D.closed_core ∪
        e '' closure (connectedComponent D.boundary_neck.center \ D.closed_core) =
        connectedComponent C.boundary_neck.center := by
      rw [← image_union, D.closed_core_union_closure_exterior, hcomponent]
    have hunion : A ∪ D.carrier = connectedComponent C.boundary_neck.center := by
      apply Subset.antisymm
      · apply union_subset hAcomp
        rw [← hcarrier, ← hcomponent]
        exact image_mono D.carrier_subset_boundary_component
      · rw [← hclosed]
        apply union_subset _ (houtside.trans subset_union_left)
        apply Subset.trans _ subset_union_right
        rw [← hcarrier]
        exact image_mono D.closed_core_subset_carrier
    refine ⟨hunion, ?_⟩
    rw [hunion, ← hclosed]
    exact (D.closed_core_compact.image e.continuous).union hc

end PoincareConjecture.CapCertificate
