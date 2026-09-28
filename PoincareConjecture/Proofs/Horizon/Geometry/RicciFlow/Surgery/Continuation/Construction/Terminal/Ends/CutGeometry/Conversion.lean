import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CutGeometry.Sides
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Orientation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.EndCorrespondence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Flow.TerminalPolicy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

private theorem exists_endCut_of_positive_frontier_region (N : EpsilonNeck g)
    (hsep : N.IsSeparating) {V : Set M} (hVo : IsOpen V) (hVc : IsConnected V)
    (hfV : frontier V = N.central_sphere)
    (hescape : ∀ K : Set M, IsCompact K → ¬ V ⊆ K)
    {q : M} (hqV : q ∈ V) (hq : q ∈ N.region 0 N.epsilon⁻¹) :
    ∃ D : SurgeryEndCut N, D.tail = V := by
  have hVS : V ⊆ N.central_sphereᶜ := by
    intro x hx hs
    exact (hfV.symm ▸ hs).2 (hVo.interior_eq.symm ▸ hx)
  have heq : V = connectedComponentIn N.central_sphereᶜ q := by
    apply Subset.antisymm (hVc.isPreconnected.subset_connectedComponentIn hqV hVS)
    apply (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      isPreconnected_connectedComponentIn ?_ ?_).trans interior_subset
    · apply disjoint_left.mpr
      intro x hx hxf
      exact connectedComponentIn_subset _ _ hx (hfV ▸ hxf)
    · exact ⟨q, mem_connectedComponentIn (hVS hqV), hVo.interior_eq.symm ▸ hqV⟩
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨p, hp⟩ := (N.isConnected_region le_rfl hi.le (neg_lt_zero.mpr hi)).nonempty
  obtain ⟨_, _, _, _, hdis, hneg, hpos, _, _, _, _⟩ :=
    N.complementary_component_frontiers hsep hp hq
  refine ⟨{
    point := q
    point_positive := hq
    tail := V
    component_eq := heq
    frontier_eq := hfV
    escapes_compact := hescape
    positive_subset := ?_
    negative_disjoint := ?_ }, rfl⟩
  · rwa [heq]
  · rw [heq]
    exact hdis.mono_left hneg

theorem exists_oriented_endCut_of_frontier_region (N : EpsilonNeck g)
    (hsep : N.IsSeparating) {V : Set M} (hVo : IsOpen V) (hVc : IsConnected V)
    (hfV : frontier V = N.central_sphere)
    (hescape : ∀ K : Set M, IsCompact K → ¬ V ⊆ K) :
    (∃ D : SurgeryEndCut N, D.tail = V) ∨
      (∃ D : SurgeryEndCut N.reversed, D.tail = V) := by
  have hc : N.center ∈ closure V :=
    frontier_subset_closure (hfV.symm ▸ N.center_on_central_sphere)
  obtain ⟨q, hqN, hqV⟩ := mem_closure_iff.mp hc N.carrier N.carrier_open
    (N.central_sphere_subset N.center_on_central_sphere)
  rcases N.carrier_subset_region_union_central_union_region hqN with (hneg | hs) | hpos
  · right
    apply exists_endCut_of_positive_frontier_region N.reversed
      (N.reversed_isSeparating.mpr hsep) hVo hVc hfV hescape hqV
    simpa only [reversed_region, reversed_epsilon, neg_inv, neg_zero] using hneg
  · exact False.elim ((hfV.symm ▸ hs).2 (hVo.interior_eq.symm ▸ hqV))
  · exact Or.inl (exists_endCut_of_positive_frontier_region N hsep hVo hVc hfV hescape hqV hpos)

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.HornEndCut

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon delta rho : ℝ}
  {E : GeneralizedFlowExtension F T} {horn : StrongHorn E epsilon}
  {N : TerminalStrongNeck E delta}

theorem exists_oriented_surgeryEndCut_or_compact_filling (cut : HornEndCut horn N rho)
    (hdelta : delta < 1 / 2) (hN : N.carrier ⊆ horn.carrier) :
    (∃ D : SurgeryEndCut (N.spatialNeck hdelta), D.tail = cut.carrier) ∨
      (∃ D : SurgeryEndCut (N.reversed.spatialNeck hdelta), D.tail = cut.carrier) ∨
      ∃ K : Set (E.extended.slice T).carrier, IsCompact K ∧ K ⊆ horn.carrier ∧
        frontier K = N.central_sphere ∧ (interior K).Nonempty := by
  obtain ⟨U, V, _, hVo, _, hVc, _, _, _, hfV, hfcV, hiV, _, hVH, _, halt⟩ :=
    horn.exists_contained_neck_partition N hdelta hN
  rcases halt with he | hcompact
  · have hVC : V = cut.carrier := he.trans cut.carrier_eq_escapingComponent.symm
    have hescape : ∀ K : Set (E.extended.slice T).carrier, IsCompact K → ¬ V ⊆ K := by
      simpa only [hVC] using cut.escapes_compact
    rcases (N.spatialNeck hdelta).exists_oriented_endCut_of_frontier_region
        (horn.contained_neck_isSeparating N hdelta hN) hVo hVc hfV hescape with h | h
    · exact Or.inl (by simpa only [hVC] using h)
    · exact Or.inr (Or.inl (by simpa only [N.reversed_spatialNeck hdelta, hVC] using h))
  · exact Or.inr (Or.inr ⟨closure V, hcompact, hVH, hfcV, hiV⟩)

end PoincareConjecture.HornEndCut
