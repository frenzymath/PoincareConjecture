import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Selection.ScalarBarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Selection.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.EndCorrespondence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon)

theorem endCut_tail_subset_carrier_of_retained_point
    {delta : ℝ} (N : TerminalStrongNeck E delta) (hdelta : delta < 1 / 2)
    (hN : N.carrier ⊆ horn.carrier) (C : SurgeryEndCut (N.spatialNeck hdelta))
    {p : (E.extended.slice T).carrier}
    (hpcomp : p ∈ connectedComponent N.center) (hpC : p ∉ C.tail)
    (hpH : p ∉ horn.carrier) : C.tail ⊆ horn.carrier := by
  obtain ⟨U, V, hUo, hVo, hUc, _, hdis, hcover, _, _, _, _, _, hVH, _⟩ :=
    horn.exists_contained_neck_partition N hdelta hN
  have hV : V ⊆ horn.carrier := subset_closure.trans hVH
  have hCcover : C.tail ⊆ U ∪ V := by
    rw [hcover]
    exact fun x hx => ⟨C.tail_subset_component hx,
      disjoint_left.mp C.tail_disjoint_central hx⟩
  rcases C.tail_isConnected.isPreconnected.subset_or_subset hUo hVo hdis hCcover with h | h
  · have hpU : p ∈ U := by
      have hpUV : p ∈ U ∪ V := by
        rw [hcover]
        exact ⟨hpcomp, fun hs => hpH (hN (N.central_sphere_subset hs))⟩
      exact hpUV.resolve_right (fun hv => hpH (hV hv))
    have hUC : U ⊆ C.tail := by
      rw [C.component_eq]
      apply hUc.isPreconnected.subset_connectedComponentIn
        (h (C.positive_subset C.point_positive))
      intro x hx
      exact (hcover ▸ (show x ∈ U ∪ V from Or.inl hx)).2
    exact False.elim (hpC (hUC hpU))
  · exact h.trans hV

end PoincareConjecture.StrongHorn

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E} (e : TerminalEnd K)

theorem exists_tail_subset_horn_cut_of_overlapping_necks
    {epsilon delta rho constant h : ℝ} (horn : StrongHorn E epsilon)
    (N P : TerminalStrongNeck E delta) (hdelta : delta ≤ 1 / 200)
    (hhalf : delta < 1 / 2) (C : SurgeryEndCut (N.spatialNeck hhalf))
    (D : HornEndCut horn P rho)
    (hrho : 0 < rho) (hconstant : 0 < constant) (hh : 0 < h)
    (hhd : h ≤ rho * delta) (hhC : h ≤ rho / (2 * constant))
    (hlevel : (E.extended.connection T).scalarCurvature N.center = h⁻¹ ^ 2)
    (hboundary : ∀ x ∈ horn.boundary_sphere,
      (E.extended.connection T).scalarCurvature x < 32 * constant * rho⁻¹ ^ 2)
    (hP : P.carrier ⊆ horn.carrier) (hmeet : (N.carrier ∩ P.carrier).Nonempty)
    {p : (E.extended.slice T).carrier}
    (hpcomp : p ∈ connectedComponent N.center) (hpC : p ∉ C.tail)
    (hpH : p ∉ horn.carrier)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ C.tail) :
    ∃ m, n ≤ m ∧ Subtype.val '' e.tail m ⊆ D.carrier := by
  have hNH : N.carrier ⊆ horn.carrier :=
    horn.neck_carrier_subset_of_overlap_of_linear_boundary N hdelta hrho hconstant hh
      hhd hhC hlevel hboundary (hmeet.mono (inter_subset_inter_right _ hP))
  exact e.exists_tail_subset_hornEndCut D n
    (htail.trans (horn.endCut_tail_subset_carrier_of_retained_point N hhalf hNH C
      hpcomp hpC hpH))

end PoincareConjecture.TerminalEnd
