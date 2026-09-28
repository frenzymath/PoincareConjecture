import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.BoundaryTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.CoreExpansion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_slice_alignment_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
          ∀ {a : ℝ}, a ∈ Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹ →
          (∀ q : UnitTwoSphere, D.boundary_neck.coordinate_map (q, a) ∈ C.end_neck.carrier) →
          ∃ e f : M ≃ₜ M, e '' C.carrier = C.carrier ∧ f '' D.carrier = D.carrier ∧
            e '' C.boundary_sphere =
              range (fun q : UnitTwoSphere => D.boundary_neck.coordinate_map (q, a)) ∧
            f '' D.boundary_sphere =
              range (fun q : UnitTwoSphere => D.boundary_neck.coordinate_map (q, a)) ∧
            C.closed_core ⊆ e '' C.closed_core := by
  obtain ⟨ε₀, hε₀, hsmall, hgraph⟩ := EpsilonNeck.exists_contained_coordinate_slice_graph.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hC hDC a ha hslice
  obtain ⟨t, ht, htslice⟩ := C.exists_boundary_slice_in_end
  obtain ⟨h, hh, hdom, heq⟩ := hgraph C.end_neck C.boundary_neck
    (C.end_neck_epsilon.trans_le hC) (C.boundary_neck_epsilon.trans_le hC) ht htslice
  obtain ⟨j, hj, jdom, jeq⟩ := hgraph C.end_neck D.boundary_neck
    (C.end_neck_epsilon.trans_le hC)
    ((D.boundary_neck_epsilon.trans hDC).trans_le hC) ha hslice
  obtain ⟨r, hr, hrN, hbound⟩ := C.end_neck.exists_graph_collar h hh hdom
  obtain ⟨s, hs, hsN, jbound⟩ := C.end_neck.exists_graph_collar j hj jdom
  obtain ⟨b, hb, hbB, htbound⟩ :=
    C.boundary_neck.exists_graph_collar (fun _ => t) continuous_const (fun _ => ht)
  obtain ⟨d, hd, hdB, habound⟩ :=
    D.boundary_neck.exists_graph_collar (fun _ => a) continuous_const (fun _ => ha)
  let B := C.boundary_neck.graphTransport hb hbB (fun _ => t) continuous_const htbound
  let H := C.end_neck.graphTransport hr hrN h hh hbound
  let J := C.end_neck.graphTransport hs hsN j hj jbound
  let e := (B.trans H.symm).trans J
  let f := D.boundary_neck.graphTransport hd hdB (fun _ => a) continuous_const habound
  have hHfix {x : M} (hx : x ∉ C.end_neck.carrier) : H x = x :=
    C.end_neck.graphTransport_fixed hr hrN h hh hbound
      (fun hxK => hx (C.end_neck.closedCollar_subset_carrier hrN hxK))
  have hHinvfix {x : M} (hx : x ∉ C.end_neck.carrier) : H.symm x = x := by
    apply H.injective
    rw [H.apply_symm_apply, hHfix hx]
  have hJfix {x : M} (hx : x ∉ C.end_neck.carrier) : J x = x :=
    C.end_neck.graphTransport_fixed hs hsN j hj jbound
      (fun hxK => hx (C.end_neck.closedCollar_subset_carrier hsN hxK))
  have hefix : EqOn e id C.carrierᶜ := by
    intro x hx
    have hBfix : B x = x := C.boundary_neck.graphTransport_fixed hb hbB _ continuous_const
      htbound (fun hxK => hx (C.boundary_neck_subset
        (C.boundary_neck.closedCollar_subset_carrier hbB hxK)))
    have hxend : x ∉ C.end_neck.carrier := fun hxend => hx (C.end_neck_subset hxend)
    change J (H.symm (B x)) = x
    rw [hBfix, hHinvfix hxend, hJfix hxend]
  have hffix : EqOn f id D.carrierᶜ := by
    intro x hx
    exact D.boundary_neck.graphTransport_fixed hd hdB _ continuous_const habound
      (fun hxK => hx (D.boundary_neck_subset
        (D.boundary_neck.closedCollar_subset_carrier hdB hxK)))
  have hecarrier : e '' C.carrier = C.carrier := by
    have hi := hefix.image_eq_self
    rw [e.image_compl] at hi
    exact compl_injective hi
  have hfcarrier : f '' D.carrier = D.carrier := by
    have hi := hffix.image_eq_self
    rw [f.image_compl] at hi
    exact compl_injective hi
  have hBimage : B '' C.boundary_sphere =
      range (fun q : UnitTwoSphere => C.boundary_neck.coordinate_map (q, t)) := by
    rw [C.boundary_eq_neck_sphere]
    exact C.boundary_neck.graphTransport_image_central_sphere hb hbB _ continuous_const htbound
  have hHimage : H '' C.end_neck.central_sphere =
      range (fun q => C.end_neck.coordinate_map (q, h q)) :=
    C.end_neck.graphTransport_image_central_sphere hr hrN h hh hbound
  have hJimage : J '' C.end_neck.central_sphere =
      range (fun q => C.end_neck.coordinate_map (q, j q)) :=
    C.end_neck.graphTransport_image_central_sphere hs hsN j hj jbound
  have hBHimage : H.symm '' (B '' C.boundary_sphere) = C.end_neck.central_sphere := by
    rw [hBimage, heq, ← hHimage]
    exact H.toEquiv.symm_image_image C.end_neck.central_sphere
  refine ⟨e, f, hecarrier, hfcarrier, ?_, ?_, ?_⟩
  · change (J ∘ (H.symm ∘ B)) '' C.boundary_sphere = _
    rw [image_comp, image_comp, hBHimage, hJimage, ← jeq]
  · rw [D.boundary_eq_neck_sphere]
    exact D.boundary_neck.graphTransport_image_central_sphere hd hdB _ continuous_const habound
  · intro x hx
    obtain ⟨y, hy, hBy⟩ := C.closed_core_subset_graphTransport_of_graph_in_end
      hb hbB (fun _ => t) continuous_const htbound htslice hx
    have hxend : x ∉ C.end_neck.carrier := Set.disjoint_left.mp C.disjoint_closed_core_end hx
    refine ⟨y, hy, ?_⟩
    change J (H.symm (B y)) = x
    rw [hBy, hHinvfix hxend, hJfix hxend]

end PoincareConjecture.CapCertificate
