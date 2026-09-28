import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.SphereTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.BoundaryTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Separation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.NeckContainment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.NonFilling

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem boundary_end_smooth_transport_of_epsilon_le
    (C : CapCertificate g) (hC : C.epsilon ≤ 1 / 200) :
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ C.carrier ∧ (∀ x, x ∉ K → D x = x) ∧
      D '' C.boundary_sphere = C.end_neck.central_sphere := by
  obtain ⟨a, ha, hslice⟩ := C.exists_boundary_slice_in_end
  obtain ⟨D, K, hK, hsub, hfix, hsphere⟩ :=
    C.end_neck.contained_slice_smooth_transport_of_epsilon_le C.boundary_neck
      (C.end_neck_epsilon.trans_le hC) (C.boundary_neck_epsilon.trans_le hC) ha hslice
  refine ⟨D, K, hK, hsub.trans (union_subset C.end_neck_subset C.boundary_neck_subset),
    hfix, ?_⟩
  rwa [C.boundary_eq_neck_sphere]

theorem end_neck_isSeparating_of_epsilon_le (C : CapCertificate g)
    (hC : C.epsilon ≤ 1 / 200) : C.end_neck.IsSeparating := by
  obtain ⟨D, K, _, _, _, hsphere⟩ := C.boundary_end_smooth_transport_of_epsilon_le hC
  have hS : D '' C.boundary_neck.central_sphere = C.end_neck.central_sphere := by
    rwa [C.boundary_eq_neck_sphere] at hsphere
  have hcomponent : D '' connectedComponent C.boundary_neck.center =
      connectedComponent C.end_neck.center := by
    have h := D.toHomeomorph.image_connectedComponentIn (s := univ)
      (x := C.boundary_neck.center) (mem_univ _)
    simp only [connectedComponentIn_univ, image_univ, D.toHomeomorph.surjective.range_eq] at h
    apply h.trans
    symm
    apply connectedComponent_eq
    apply C.end_neck.carrier_subset_connectedComponent
    apply C.end_neck.central_sphere_subset
    rw [← hS]
    exact mem_image_of_mem D C.boundary_neck.center_on_central_sphere
  exact (C.boundary_neck.isSeparating_iff_of_homeomorph C.end_neck D.toHomeomorph
    hcomponent hS).mp C.boundary_neck_isSeparating

theorem exists_compact_filling_end_sphere_of_epsilon_le
    (C : CapCertificate g) (hC : C.epsilon ≤ 1 / 200) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ C.carrier ∧
      frontier K = C.end_neck.central_sphere ∧ (interior K).Nonempty := by
  obtain ⟨D, L, _, hLC, hfix, hsphere⟩ := C.boundary_end_smooth_transport_of_epsilon_le hC
  have hcarrier : D '' C.carrier = C.carrier :=
    DeepHorn.image_eq_self_of_fixed_compl D.toHomeomorph
      (fun x hx => hfix x (fun h => hx (hLC h)))
  refine ⟨D '' C.closed_core, C.closed_core_compact.image D.continuous, ?_, ?_, ?_⟩
  · rw [← hcarrier]
    exact image_mono C.closed_core_subset_carrier
  · change frontier (D.toHomeomorph '' C.closed_core) = C.end_neck.central_sphere
    rw [← D.toHomeomorph.image_frontier, C.core_frontier_eq_boundary]
    exact hsphere
  · change (interior (D.toHomeomorph '' C.closed_core)).Nonempty
    rw [← D.toHomeomorph.image_interior, ← C.core_eq_interior_closed_core]
    exact C.core_nonempty.image D

theorem closed_core_neck_noncontainment_of_epsilon_le
    (C : CapCertificate g) (N : EpsilonNeck g)
    (hC : C.epsilon ≤ 1 / 200) (hN : N.epsilon ≤ 1 / 200) :
    ¬ C.closed_core ⊆ N.carrier := by
  intro hsub
  have hzero : (0 : ℝ) ∈ Ioo (-C.boundary_neck.epsilon⁻¹) C.boundary_neck.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr C.boundary_neck.epsilon_pos),
      inv_pos.mpr C.boundary_neck.epsilon_pos⟩
  have hmem (q : UnitTwoSphere) : C.boundary_neck.coordinate_map (q, 0) ∈ N.carrier := by
    apply hsub
    apply C.boundary_subset_closed_core
    rw [C.boundary_eq_neck_sphere, ← C.boundary_neck.centralSphere_range]
    exact mem_range_self q
  obtain ⟨h, hh, hdom, hgraph, _⟩ := N.sphereSlice_graph_and_isotopy_of_epsilon_le
    C.boundary_neck hN (C.boundary_neck_epsilon.trans_le hC) hzero hmem
  obtain ⟨D, L, _, hLN, hfix, _, hsphere⟩ := N.exists_smooth_graph_transport h hh hdom
  have hboundary : D '' N.central_sphere = C.boundary_sphere := by
    rw [hsphere, ← hgraph, C.boundary_eq_neck_sphere, C.boundary_neck.centralSphere_range]
  have hcore : D.symm '' C.closed_core ⊆ N.carrier := by
    rintro y ⟨x, hx, rfl⟩
    by_contra hout
    have h := hfix (D.symm x) (fun h => hout (hLN h))
    rw [D.apply_symm_apply] at h
    exact hout (h ▸ hsub hx)
  have hfront : frontier (D.symm '' C.closed_core) = N.central_sphere := by
    change frontier (D.symm.toHomeomorph '' C.closed_core) = N.central_sphere
    rw [← D.symm.toHomeomorph.image_frontier, C.core_frontier_eq_boundary, ← hboundary]
    exact D.toEquiv.symm_image_image _
  have hint : (interior (D.symm '' C.closed_core)).Nonempty := by
    change (interior (D.symm.toHomeomorph '' C.closed_core)).Nonempty
    rw [← D.symm.toHomeomorph.image_interior, ← C.core_eq_interior_closed_core]
    exact C.core_nonempty.image D.symm
  exact N.not_isCompact_of_frontier_eq_central_sphere hcore hfront hint
    (C.closed_core_compact.image D.symm.continuous)

theorem carrier_subset_core_of_disjoint_boundary_of_epsilon_le
    (C D : CapCertificate g) (hC : C.epsilon ≤ 1 / 200) (hD : D.epsilon ≤ 1 / 200)
    (hCD : C.carrier ⊆ D.carrier) (hdis : Disjoint C.carrier D.boundary_sphere) :
    C.carrier ⊆ D.core := by
  rcases D.subset_core_or_compl_closed_core C.isConnected_carrier.isPreconnected hdis with h | h
  · exact h
  · exfalso
    apply C.closed_core_neck_noncontainment_of_epsilon_le D.end_neck hC
      (D.end_neck_epsilon.trans_le hD)
    intro x hx
    have hxC := C.closed_core_subset_carrier hx
    by_contra hout
    apply h hxC
    rw [D.closed_core_eq_complement_end]
    exact ⟨hCD hxC, hout⟩

end PoincareConjecture.CapCertificate
