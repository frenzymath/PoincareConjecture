import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.EnclosingRegion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem subset_open_of_disjoint_frontier {A U : Set M}
    (hA : IsConnected A) (hU : IsOpen U)
    (hmeet : (U ∩ A).Nonempty) (hdis : Disjoint A (frontier U)) : A ⊆ U := by
  let : ConnectedSpace A := isConnected_iff_connectedSpace.mp hA
  have hopen := isClopen_preimage_val hU hdis.symm
  obtain ⟨x, hxU, hx⟩ := hmeet
  have heq := hopen.eq_univ ⟨⟨x, hx⟩, hxU⟩
  intro y hy
  exact (show (⟨y, hy⟩ : A) ∈ Subtype.val ⁻¹' U from heq ▸ mem_univ _)

theorem closed_side_subset_of_transported_boundary_subset (C D : CapCertificate g)
    (e : M ≃ₜ M) (hboundary : e '' D.boundary_sphere ⊆ C.carrier) :
    e '' D.closed_core ⊆ C.carrier ∨
      (IsCompact (e '' closure (connectedComponent D.boundary_neck.center \ D.closed_core)) ∧
        e '' closure (connectedComponent D.boundary_neck.center \ D.closed_core) ⊆
          C.carrier) := by
  have hDs : IsCompact D.boundary_sphere :=
    D.closed_core_compact.of_isClosed_subset
      (D.core_frontier_eq_boundary ▸ isClosed_frontier) D.boundary_subset_closed_core
  obtain ⟨U, hU, hcompact, hUC, hDU, hconn⟩ :=
    C.exists_enclosing_region (hDs.image e.continuous) hboundary
  let V := e.symm '' U
  have hV : IsOpen V := e.symm.isOpenMap U hU
  have hVcompact : IsCompact (closure V) := by
    rw [← e.symm.image_closure]
    exact hcompact.image e.symm.continuous
  have hVC : e '' closure V ⊆ C.carrier := by
    rw [← e.symm.image_closure]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa only [e.apply_symm_apply] using hUC hy
  have hDV : D.boundary_sphere ⊆ V := by
    intro x hx
    exact ⟨e x, hDU (mem_image_of_mem e hx), e.symm_apply_apply x⟩
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
      (image_mono hcl).trans hVC⟩
  · left
    have hsub : D.core ⊆ V := by
      apply subset_open_of_disjoint_frontier D.isConnected_core hV hcoremeet
      exact disjoint_left.mpr (fun x hx hxF => hext hxF (D.core_subset_closed_core hx))
    rw [← D.closure_core_eq_closed_core]
    exact (image_mono (closure_mono hsub)).trans hVC

theorem compact_component_of_transported_boundary_subset (C D : CapCertificate g)
    (e : M ≃ₜ M) (hboundary : e '' D.boundary_sphere ⊆ C.carrier)
    (hcarrier : e '' D.carrier = D.carrier)
    (hcontact : (frontier C.carrier ∩ (e '' D.closed_core)).Nonempty) :
    C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center ∧
      IsCompact (C.carrier ∪ D.carrier) := by
  rcases C.closed_side_subset_of_transported_boundary_subset D e hboundary with
    hinside | ⟨hc, houtside⟩
  · obtain ⟨x, hx, hxD⟩ := hcontact
    exact False.elim ((C.carrier_open.frontier_eq ▸ hx).2 (hinside hxD))
  · have hcenter : e D.boundary_neck.center ∈ C.carrier := by
      apply hboundary
      apply mem_image_of_mem
      rw [D.boundary_eq_neck_sphere]
      exact D.boundary_neck.center_on_central_sphere
    have hcomponent : e '' connectedComponent D.boundary_neck.center =
        connectedComponent C.boundary_neck.center := by
      have h := e.image_connectedComponentIn (s := univ)
        (x := D.boundary_neck.center) (mem_univ _)
      simp only [image_univ, e.surjective.range_eq, connectedComponentIn_univ] at h
      exact h.trans (connectedComponent_eq (C.carrier_subset_boundary_component hcenter)).symm
    have hclosed : e '' D.closed_core ∪
        e '' closure (connectedComponent D.boundary_neck.center \ D.closed_core) =
        connectedComponent C.boundary_neck.center := by
      rw [← image_union, D.closed_core_union_closure_exterior, hcomponent]
    have hunion : C.carrier ∪ D.carrier = connectedComponent C.boundary_neck.center := by
      apply Subset.antisymm
      · apply union_subset C.carrier_subset_boundary_component
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
