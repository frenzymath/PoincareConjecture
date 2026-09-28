import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SharedBandJoinFrontier
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinRelativeCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_straight_join_bands_cover_region
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {s A B t c : ℝ} (hsA : s < A) (hBt : B < t) (hc : 0 < c)
    (hai : InjOn alpha (Icc s A)) (hbi : InjOn beta (Icc B t))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A)
    {D U V : Set AnnulusCoordinates} (hD : IsCompact D) (hpD : alpha A ∉ D)
    (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (hfU : frontier U = (alpha '' Icc s A ∪ beta '' Icc B t) ∪ D)
    (hfV : frontier V = frontier U)
    (L L' : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {lo lo' : ℝ → ℝ} {a b ua wa ub wb ra r a' b' ua' wa' ub' wb' rb' : ℝ}
    (C : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      lo a b ua wa ub wb ra r)
    (C' : ObliqueBandFaces
      (collarParameterEquiv.trans L').toHomeomorph.toOpenPartialHomeomorph
      lo' a' b' ua' wa' ub' wb' r rb')
    {d : AnnulusCoordinates}
    (hbase : L (b, lo b) = alpha A) (hbase' : L' (a', lo' a') = alpha A)
    (hdir : L (ub, wb) = d) (hdir' : L' (ua', wa') = d)
    (hinter : C.carrier ∩ C'.carrier = segment ℝ (alpha A) (alpha A + r • d))
    (hlower : C.lowerArc ⊆ alpha '' Icc s A) (hlower' : C'.lowerArc ⊆ beta '' Icc B t)
    (hsub : C.carrier ⊆ closure U) (hsub' : C'.carrier ⊆ closure U) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ alpha A ∈ W ∧
      W ∩ closure U ⊆ C.carrier ∪ C'.carrier := by
  obtain ⟨N, hN, hpN, hfront⟩ :=
    m64Intrinsic_exists_shared_band_join_frontier_neighborhood L L' C C'
      hbase hbase' hdir hdir' hinter
  let K := C.carrier ∪ C'.carrier
  have hK : IsClosed K := C.isClosed_carrier.union C'.isClosed_carrier
  have hregular : closure (interior K) = K := by
    apply subset_antisymm (closure_minimal interior_subset hK)
    rintro z (hz | hz)
    · rw [← C.closure_interior_carrier] at hz
      exact closure_mono (interior_mono (subset_union_left : C.carrier ⊆ K)) hz
    · rw [← C'.closure_interior_carrier] at hz
      exact closure_mono (interior_mono (subset_union_right : C'.carrier ⊆ K)) hz
  have hpK : alpha A ∈ K := by
    left
    apply C.isClosed_carrier.frontier_subset
    apply C.endpointEdge_subset_frontier true
    refine ⟨0, by norm_num, ?_⟩
    rw [m64Intrinsic_band_right_endpoint_zero]
    exact hbase
  apply m64Intrinsic_exists_straight_join_relative_cover ha hb hsA hBt hc hai hbi
    hend hreg htan hD hpD hU hV hd hfU hfV hK hregular
    (union_subset hsub hsub') hpK (hN.mem_nhds hpN)
  intro z hz
  rw [hfU]
  exact Or.inl ((union_subset_union hlower hlower') (hfront hz))

end PoincareConjecture
