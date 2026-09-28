import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MatchedBandJoinFrontier
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcRelativeBoundaryCover





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_arc_matched_bands_cover_region
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B p : ℝ}
    (hinj : InjOn gamma (Icc A B))
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0) (hp : p ∈ Ioo A B)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : gamma p ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma '' Icc A B ∪ K) (hfV : frontier V = frontier U)
    {F F' : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f g : ℝ → ℝ} {a b ua wa ub wb ra rb a' b' ua' wa' ub' wb' ra' rb' : ℝ}
    (C : ObliqueBandFaces F f a b ua wa ub wb ra rb)
    (D : ObliqueBandFaces F' g a' b' ua' wa' ub' wb' ra' rb')
    (right right' : Bool)
    (hbase : (C.endpointEdge right).map 0 = gamma p)
    (hbase' : (D.endpointEdge right').map 0 = gamma p)
    (hcut : (C.endpointEdge right).map '' Icc (0 : ℝ) 1 =
      (D.endpointEdge right').map '' Icc (0 : ℝ) 1)
    (hinter : C.carrier ∩ D.carrier ⊆ frontier C.carrier)
    (hlowerC : C.lowerArc ⊆ gamma '' Icc A B)
    (hlowerD : D.lowerArc ⊆ gamma '' Icc A B)
    (hsubC : C.carrier ⊆ closure U) (hsubD : D.carrier ⊆ closure U) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧
      W ∩ closure U ⊆ C.carrier ∪ D.carrier := by
  obtain ⟨N, hN, hpN, hfrontN⟩ :=
    m64Intrinsic_exists_matched_band_join_frontier_neighborhood C D right right'
      hbase hbase' hcut hinter
  have hclosed : IsClosed (C.carrier ∪ D.carrier) :=
    C.isClosed_carrier.union D.isClosed_carrier
  have hreg : closure (interior (C.carrier ∪ D.carrier)) = C.carrier ∪ D.carrier := by
    apply subset_antisymm (closure_minimal interior_subset hclosed)
    rintro z (hz | hz)
    · rw [← C.closure_interior_carrier] at hz
      exact closure_mono (interior_mono subset_union_left) hz
    · rw [← D.closure_interior_carrier] at hz
      exact closure_mono (interior_mono subset_union_right) hz
  have hpoint : gamma p ∈ C.carrier ∪ D.carrier := by
    left
    apply C.isClosed_carrier.frontier_subset
    exact C.endpointEdge_subset_frontier right ⟨0, by norm_num, hbase⟩
  apply m64Intrinsic_exists_arc_relative_cover_of_local_frontier hg hinj hregular hp
    hK hpK hU hV hUV hfront (hfV.trans hfront) hclosed hreg
    (union_subset hsubC hsubD) hpoint (hN.mem_nhds hpN)
  exact fun z hz => Or.inl ((union_subset hlowerC hlowerD) (hfrontN hz))

end PoincareConjecture
