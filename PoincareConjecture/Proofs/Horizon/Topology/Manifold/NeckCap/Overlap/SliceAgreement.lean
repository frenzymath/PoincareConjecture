import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SliceProjection












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_contained_slice_compact_transport :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon ≤ ε₀ →
        ∀ {a : ℝ}, a ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ →
        (∀ q : UnitTwoSphere, P.coordinate_map (q, a) ∈ N.carrier) →
          ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ N.carrier ∪ P.carrier ∧
            (∀ x, x ∉ K → e x = x) ∧
            e '' connectedComponent P.center = connectedComponent N.center ∧
            e '' P.central_sphere = N.central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, hgraph⟩ := exists_contained_coordinate_slice_graph.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hN hP a ha hmem
  obtain ⟨h, hh, hdom, hslice⟩ := hgraph N P hN hP ha hmem
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar h hh hdom
  obtain ⟨s, hs, hsP, habound⟩ :=
    P.exists_graph_collar (fun _ => a) continuous_const (fun _ => ha)
  let eN := N.graphTransport hr hrN h hh hbound
  let eP := P.graphTransport hs hsP (fun _ => a) continuous_const habound
  have hNsphere : eN '' N.central_sphere =
      range (fun q : UnitTwoSphere => P.coordinate_map (q, a)) :=
    (N.graphTransport_image_central_sphere hr hrN h hh hbound).trans hslice.symm
  have hPsphere : eP '' P.central_sphere =
      range (fun q : UnitTwoSphere => P.coordinate_map (q, a)) :=
    P.graphTransport_image_central_sphere hs hsP (fun _ => a) continuous_const habound
  have hcomponent : connectedComponent P.center = connectedComponent N.center := by
    let q := (P.coordinate_inverse P.center).1
    have hxP : P.coordinate_map (q, a) ∈ P.carrier :=
      P.coordinate_map_mem ⟨mem_univ q, ha⟩
    exact (connectedComponent_eq (P.carrier_subset_connectedComponent hxP)).trans
      (connectedComponent_eq (N.carrier_subset_connectedComponent (hmem q))).symm
  refine ⟨eP.trans eN.symm, N.closedCollar r ∪ P.closedCollar s,
    (N.isCompact_closedCollar hrN).union (P.isCompact_closedCollar hsP),
    union_subset_union (N.closedCollar_subset_carrier hrN) (P.closedCollar_subset_carrier hsP),
    ?_, ?_, ?_⟩
  · intro x hx
    have hxN : x ∉ N.closedCollar r := fun h => hx (Or.inl h)
    have hxP : x ∉ P.closedCollar s := fun h => hx (Or.inr h)
    have hfixP : eP x = x :=
      P.graphTransport_fixed hs hsP (fun _ => a) continuous_const habound hxP
    have hfixN : eN x = x := N.graphTransport_fixed hr hrN h hh hbound hxN
    change eN.symm (eP x) = x
    rw [hfixP]
    exact eN.symm_apply_eq.mpr hfixN.symm
  · change (eN.symm ∘ eP) '' connectedComponent P.center = connectedComponent N.center
    rw [image_comp]
    have hPcomponent : eP '' connectedComponent P.center = connectedComponent P.center :=
      P.graphTransport_image_connectedComponent hs hsP (fun _ => a) continuous_const habound _
    have hNcomponent : eN '' connectedComponent P.center = connectedComponent P.center :=
      N.graphTransport_image_connectedComponent hr hrN h hh hbound _
    rw [hPcomponent]
    calc
      eN.symm '' connectedComponent P.center =
          eN.symm '' (eN '' connectedComponent P.center) :=
        congrArg (fun A => eN.symm '' A) hNcomponent.symm
      _ = connectedComponent P.center := eN.toEquiv.symm_image_image _
      _ = connectedComponent N.center := hcomponent
  · change (eN.symm ∘ eP) '' P.central_sphere = N.central_sphere
    rw [image_comp, hPsphere, ← hNsphere]
    exact eN.toEquiv.symm_image_image _



theorem exists_contained_slice_separation_agreement :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon ≤ ε₀ →
        ∀ {a : ℝ}, a ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ →
        (∀ q : UnitTwoSphere, P.coordinate_map (q, a) ∈ N.carrier) →
          (P.IsSeparating ↔ N.IsSeparating) ∧
            (P.IsNonseparating ↔ N.IsNonseparating) := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ := exists_contained_slice_compact_transport.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hN hP a ha hmem
  obtain ⟨e, _, _, _, _, hcomponent, hsphere⟩ := htransport N P hN hP ha hmem
  exact ⟨P.isSeparating_iff_of_homeomorph N e hcomponent hsphere,
    P.isNonseparating_iff_of_homeomorph N e hcomponent hsphere⟩

end PoincareConjecture.EpsilonNeck
