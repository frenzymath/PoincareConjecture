import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcStraightFan
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBoundaryFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalInteriorFans

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

open Classical in

theorem m64Intrinsic_digon_regular_vertex_fan
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ}
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hareg : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (v : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v.1 ≠ alpha 0) (hv1 : v.1 ≠ alpha A) :
    coordinateVertexAngleContribution g R.coordinates R.basis v.1 =
      if v.1 ∈ frontier U then Real.pi else 2 * Real.pi := by
  have hfan {eta : ℝ → AnnulusCoordinates} {a b p : ℝ}
      (he : ContDiff ℝ ∞ eta) (hei : InjOn eta (Icc a b)) (hp : p ∈ Ioo a b)
      (hr : deriv eta p ≠ 0) {K : Set AnnulusCoordinates} (hK : IsCompact K)
      (hpK : eta p ∉ K) (hf : frontier U = eta '' Icc a b ∪ K)
      (hv : v.1 = eta p) :
      coordinateVertexAngleContribution g R.coordinates R.basis v.1 = Real.pi :=
    m64Intrinsic_region_arc_boundary_fan R.face R.coordinates R.basis R.smooth
      R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
      R.intersections R.intersection_frontier g he hei hp hr hK hpK
      hU hV hUV hf hfV R.cover v hv
  by_cases hboundary : v.1 ∈ frontier U
  · rw [if_pos hboundary]
    rw [hfront] at hboundary
    rcases hboundary with ⟨p, hp, hpv⟩ | ⟨p, hp, hpv⟩
    · have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
        hv0 (hpv.symm.trans (congrArg alpha h.symm)))
      have hpA : p < A := lt_of_le_of_ne hp.2 (fun h =>
        hv1 (hpv.symm.trans (congrArg alpha h)))
      have hpK : alpha p ∉ beta '' Icc 0 B := by
        rintro ⟨t, ht, he⟩
        rcases hmeet p hp t ht he.symm with h | h
        · exact hp0.ne' h.1
        · exact hpA.ne h.1
      exact hfan ha hai ⟨hp0, hpA⟩ (hareg p ⟨hp0, hpA⟩)
        (isCompact_Icc.image hb.continuous) hpK hfront hpv.symm
    · have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
        hv0 (hpv.symm.trans ((congrArg beta h.symm).trans hbase)))
      have hpB : p < B := lt_of_le_of_ne hp.2 (fun h =>
        hv1 (hpv.symm.trans ((congrArg beta h).trans hend)))
      have hpK : beta p ∉ alpha '' Icc 0 A := by
        rintro ⟨t, ht, he⟩
        rcases hmeet t ht p hp he with h | h
        · exact hp0.ne' h.2
        · exact hpB.ne h.2
      exact hfan hb hbi ⟨hp0, hpB⟩ (hbreg p ⟨hp0, hpB⟩)
        (isCompact_Icc.image ha.continuous) hpK
        (hfront.trans (union_comm _ _)) hpv.symm
  · rw [if_neg hboundary]
    have htrace : frontier (⋃ i, (R.face i).carrier) = frontier U := by
      rw [R.cover, (m64Intrinsic_jordan_interior_closure hU hV hUV hfV.symm).2]
    have hregion : v.1 ∈ ⋃ i, (R.face i).carrier := by
      obtain ⟨⟨i, k⟩, hik⟩ := v.2
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [R.carrier]
      exact ⟨R.basis i k, subset_convexHull ℝ _ (mem_range_self k), hik⟩
    have hinside : v.1 ∈ interior (⋃ i, (R.face i).carrier) := by
      by_contra h
      exact hboundary (htrace ▸ ⟨subset_closure hregion, h⟩)
    exact m64Intrinsic_regional_interior_vertex_fan R.face R.coordinates R.basis
      R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
      R.intersections R.intersection_frontier g v hinside

end PoincareConjecture
