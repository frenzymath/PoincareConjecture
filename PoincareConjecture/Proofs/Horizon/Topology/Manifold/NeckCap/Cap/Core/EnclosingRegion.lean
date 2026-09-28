import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ModelCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Noncompact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.ProjectiveEnclosure
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_enclosing_region_euclidean (C : CapCertificate g)
    (hkind : C.model_kind = .euclidean) {S : Set M}
    (hS : IsCompact S) (hSC : S ⊆ C.carrier) :
    ∃ U : Set M, IsOpen U ∧ IsCompact (closure U) ∧
      closure U ⊆ C.carrier ∧ S ⊆ U ∧ IsConnected (frontier U) := by
  obtain ⟨e, hs, ht, _, _⟩ := C.exists_euclidean_coordinates hkind
  have hei : Continuous e.symm := continuousOn_univ.mp (ht ▸ e.continuousOn_symm)
  have hinj : Function.Injective e.symm := by
    intro x y hxy
    have h := congrArg e hxy
    simpa only [e.right_inv (ht.symm ▸ mem_univ x),
      e.right_inv (ht.symm ▸ mem_univ y)] using h
  obtain ⟨r, hr⟩ := (hS.image_of_continuousOn
    (e.continuousOn.mono (hs.symm ▸ hSC))).isBounded.subset_ball 0
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let U := e.symm '' Metric.ball 0 R
  let K := e.symm '' Metric.closedBall 0 R
  have hU : IsOpen U := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (by simpa only [e.symm_source, ht] using subset_univ (Metric.ball 0 R))
  have hK : IsCompact K := (isCompact_closedBall 0 R).image hei
  have hcl : closure U = K := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono Metric.ball_subset_closedBall) hK.isClosed
    · simpa only [closure_ball _ hR.ne'] using
        (image_closure_subset_closure_image (s := Metric.ball 0 R) hei)
  have hKC : K ⊆ C.carrier := by
    rintro _ ⟨y, _, rfl⟩
    exact hs ▸ e.map_target (ht.symm ▸ mem_univ y)
  have hfront : frontier U = e.symm '' Metric.sphere 0 R := by
    rw [frontier, hU.interior_eq, hcl, ← image_sdiff hinj, Metric.closedBall_sdiff_ball]
  refine ⟨U, hU, hcl ▸ hK, hcl ▸ hKC, ?_, ?_⟩
  · intro x hx
    exact ⟨e x, Metric.ball_subset_ball (le_max_left _ _) (hr (mem_image_of_mem _ hx)),
      e.left_inv (hs.symm ▸ hSC hx)⟩
  · rw [hfront]
    apply (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3)) ?_ 0 hR.le).image
      _ hei.continuousOn
    rw [← Module.finrank_eq_rank]
    norm_num

theorem exists_enclosing_region (C : CapCertificate g)
    {S : Set M} (hS : IsCompact S) (hSC : S ⊆ C.carrier) :
    ∃ U : Set M, IsOpen U ∧ IsCompact (closure U) ∧
      closure U ⊆ C.carrier ∧ S ⊆ U ∧ IsConnected (frontier U) := by
  cases hk : C.model_kind with
  | euclidean => exact C.exists_enclosing_region_euclidean hk hS hSC
  | puncturedProjective => exact C.exists_enclosing_region_projective hk hS hSC

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

theorem closed_side_subset_of_boundary_subset (C D : CapCertificate g)
    (hboundary : D.boundary_sphere ⊆ C.carrier) :
    D.closed_core ⊆ C.carrier ∨
      (IsCompact (closure (connectedComponent D.boundary_neck.center \ D.closed_core)) ∧
        closure (connectedComponent D.boundary_neck.center \ D.closed_core) ⊆ C.carrier) := by
  have hDs : IsCompact D.boundary_sphere :=
    D.closed_core_compact.of_isClosed_subset
      (D.core_frontier_eq_boundary ▸ isClosed_frontier) D.boundary_subset_closed_core
  obtain ⟨U, hU, hcompact, hUC, hDU, hconn⟩ :=
    C.exists_enclosing_region hDs hboundary
  have hdis : Disjoint (frontier U) D.boundary_sphere := by
    exact disjoint_left.mpr (fun x hx hxD => hx.2 (hU.interior_eq.symm ▸ hDU hxD))
  have hp : D.boundary_neck.center ∈ D.boundary_sphere :=
    D.boundary_eq_neck_sphere.symm ▸ D.boundary_neck.center_on_central_sphere
  have hcoremeet : (U ∩ D.core).Nonempty :=
    mem_closure_iff.mp (D.closure_core_eq_closed_core.symm ▸ D.boundary_subset_closed_core hp)
      U hU (hDU hp)
  have hextmeet : (U ∩ (connectedComponent D.boundary_neck.center \ D.closed_core)).Nonempty :=
    mem_closure_iff.mp ((D.frontier_exterior_eq_boundary.symm ▸ hp).1) U hU (hDU hp)
  rcases D.subset_core_or_compl_closed_core hconn.isPreconnected hdis with hcore | hext
  · right
    have hsub : connectedComponent D.boundary_neck.center \ D.closed_core ⊆ U := by
      apply subset_open_of_disjoint_frontier D.isConnected_component_diff_closed_core hU hextmeet
      exact disjoint_left.mpr (fun x hx hxF => hx.2 (D.core_subset_closed_core (hcore hxF)))
    have hcl := closure_mono hsub
    exact ⟨hcompact.of_isClosed_subset isClosed_closure hcl, hcl.trans hUC⟩
  · left
    have hsub : D.core ⊆ U := by
      apply subset_open_of_disjoint_frontier D.isConnected_core hU hcoremeet
      exact disjoint_left.mpr (fun x hx hxF => hext hxF (D.core_subset_closed_core hx))
    rw [← D.closure_core_eq_closed_core]
    exact (closure_mono hsub).trans hUC

theorem closed_core_subset_of_nested_boundary_subset (C D : CapCertificate g)
    (hCD : C.carrier ⊆ D.carrier)
    (hboundary : D.boundary_sphere ⊆ C.carrier) : D.closed_core ⊆ C.carrier := by
  rcases C.closed_side_subset_of_boundary_subset D hboundary with h | h
  · exact h
  · have hcompact : IsCompact (connectedComponent D.boundary_neck.center) := by
      rw [← D.closed_core_union_closure_exterior]
      exact D.closed_core_compact.union h.1
    have hfull : connectedComponent D.boundary_neck.center = D.carrier := by
      apply Subset.antisymm _ D.carrier_subset_boundary_component
      rw [← D.closed_core_union_closure_exterior]
      exact union_subset D.closed_core_subset_carrier (h.2.trans hCD)
    exact False.elim (D.not_isCompact_carrier (hfull ▸ hcompact))

theorem not_boundary_subset_of_nested_frontier_contact (C D : CapCertificate g)
    (hCD : C.carrier ⊆ D.carrier)
    (hcontact : (frontier C.carrier ∩ D.closed_core).Nonempty) :
    ¬ D.boundary_sphere ⊆ C.carrier := by
  intro hboundary
  obtain ⟨x, hx, hxD⟩ := hcontact
  exact hx.2 (C.carrier_open.interior_eq.symm ▸
    C.closed_core_subset_of_nested_boundary_subset D hCD hboundary hxD)

end PoincareConjecture.CapCertificate
