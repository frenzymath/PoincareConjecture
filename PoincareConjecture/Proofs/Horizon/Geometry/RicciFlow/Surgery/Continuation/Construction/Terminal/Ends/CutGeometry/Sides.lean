import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CutGeometry.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.EndCut.Topology.Components
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.EndCut.Topology.Escaping









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon)

theorem isConnected_boundary_sphere : IsConnected horn.boundary_sphere := by
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  rw [horn.boundary_sphere_eq]
  apply (isConnected_univ.prod (isConnected_singleton : IsConnected ({0} : Set ℝ))).image
  apply horn.parameterization_smooth.continuousOn.mono
  rintro ⟨q, t⟩ ⟨_, ht⟩
  have ht0 : t = 0 := ht
  subst t
  exact ⟨mem_univ _, neg_lt_zero.mpr horn.collar_pos, by norm_num⟩



theorem exists_contained_neck_partition {delta : ℝ} (N : TerminalStrongNeck E delta)
    (hdelta : delta < 1 / 2) (hN : N.carrier ⊆ horn.carrier) :
    ∃ U V : Set (E.extended.slice T).carrier,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = connectedComponent N.center \ N.central_sphere ∧
      frontier U = N.central_sphere ∧ frontier V = N.central_sphere ∧
      frontier (closure V) = N.central_sphere ∧
      (interior (closure V)).Nonempty ∧ horn.boundary_sphere ⊆ U ∧
      closure V ⊆ horn.carrier ∧
      (∀ p ∈ V, V = connectedComponentIn (horn.carrier \ N.central_sphere) p) ∧
      (V = horn.escapingComponent N.central_sphere N.isCompact_central_sphere ∨
        IsCompact (closure V)) := by
  have hcenter := hN (N.central_sphere_subset N.center_on_central_sphere)
  have hHcomp : horn.carrier ⊆ connectedComponent N.center :=
    horn.isPreconnected_carrier.subset_connectedComponent hcenter
  have havoid : Disjoint N.central_sphere horn.boundary_sphere := by
    apply disjoint_left.mpr
    intro x hx hb
    exact horn.boundary_sphere_not_mem_interior hb
      (N.carrier_open.subset_interior_iff.mpr hN (N.central_sphere_subset hx))
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdis, hcover, hfU, hfV, hfcU, hfcV, hiU, hiV⟩ :=
    (N.spatialNeck hdelta).exists_exhaustive_complementary_regions
      (horn.contained_neck_isSeparating N hdelta hN)
  have hboundarycover : horn.boundary_sphere ⊆ U ∪ V := by
    rw [hcover]
    exact fun x hx => ⟨hHcomp (horn.boundary_sphere_subset_carrier hx),
      fun hs => disjoint_left.mp havoid hs hx⟩
  have hcase {U V : Set (E.extended.slice T).carrier}
      (hUo : IsOpen U) (hVo : IsOpen V) (hVc : IsConnected V)
      (hdis : Disjoint U V)
      (hcover : U ∪ V = connectedComponent N.center \ N.central_sphere)
      (hfV : frontier V = N.central_sphere) (hboundary : horn.boundary_sphere ⊆ U) :
      closure V ⊆ horn.carrier ∧
      (∀ p ∈ V, V = connectedComponentIn (horn.carrier \ N.central_sphere) p) ∧
      (V = horn.escapingComponent N.central_sphere N.isCompact_central_sphere ∨
        IsCompact (closure V)) := by
    have hmeet : (V ∩ horn.carrier).Nonempty := by
      have hc : N.center ∈ closure V :=
        frontier_subset_closure (hfV.symm ▸ N.center_on_central_sphere)
      obtain ⟨x, hxN, hxV⟩ := mem_closure_iff.mp hc N.carrier N.carrier_open
        (N.central_sphere_subset N.center_on_central_sphere)
      exact ⟨x, hxV, hN hxN⟩
    have hVH : V ⊆ horn.carrier := horn.subset_carrier_of_isPreconnected hVc.isPreconnected
      hmeet (hdis.symm.mono_right hboundary)
    have hVS : V ⊆ horn.carrier \ N.central_sphere := by
      intro x hx
      exact ⟨hVH hx, (hcover ▸ (show x ∈ U ∪ V from Or.inr hx)).2⟩
    have heq : ∀ p ∈ V, V = connectedComponentIn (horn.carrier \ N.central_sphere) p := by
      intro p hp
      apply Subset.antisymm (hVc.isPreconnected.subset_connectedComponentIn hp hVS)
      have hsubset : connectedComponentIn (horn.carrier \ N.central_sphere) p ⊆ U ∪ V := by
        intro x hx
        rw [hcover]
        have hh := connectedComponentIn_subset _ _ hx
        exact ⟨hHcomp hh.1, hh.2⟩
      rcases isPreconnected_connectedComponentIn.subset_or_subset hUo hVo hdis hsubset with h | h
      · exact False.elim (disjoint_left.mp hdis (h (mem_connectedComponentIn (hVS hp))) hp)
      · exact h
    refine ⟨closure_minimal hVH horn.isClosed_carrier, heq, ?_⟩
    by_cases hVe : V = horn.escapingComponent N.central_sphere N.isCompact_central_sphere
    · exact Or.inl hVe
    · right
      obtain ⟨p, hp⟩ := hVc.nonempty
      obtain ⟨b, _, hb1, hprefix⟩ := horn.component_subset_prefix_of_ne_escaping
        N.central_sphere N.isCompact_central_sphere p (by rwa [← heq p hp])
      rw [← heq p hp] at hprefix
      exact (horn.isCompact_coordinatePrefix hb1).of_isClosed_subset isClosed_closure
        (closure_minimal hprefix (horn.isCompact_coordinatePrefix hb1).isClosed)
  rcases horn.isConnected_boundary_sphere.isPreconnected.subset_or_subset
      hUo hVo hdis hboundarycover with hU | hV
  · obtain ⟨hcl, heq, halt⟩ := hcase hUo hVo hVc hdis hcover hfV hU
    exact ⟨U, V, hUo, hVo, hUc, hVc, hdis, hcover, hfU, hfV, hfcV, hiV, hU, hcl, heq, halt⟩
  · have hcover' : V ∪ U = connectedComponent N.center \ N.central_sphere :=
      union_comm V U ▸ hcover
    obtain ⟨hcl, heq, halt⟩ :=
      hcase hVo hUo hUc hdis.symm hcover' hfU hV
    exact ⟨V, U, hVo, hUo, hVc, hUc, hdis.symm, hcover', hfV, hfU, hfcU, hiU, hV,
      hcl, heq, halt⟩

end PoincareConjecture.StrongHorn
