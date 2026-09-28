import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcStraightFan
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBoundaryFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalInteriorFans





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

open Classical in




theorem m64Intrinsic_triangle_region_regular_vertex_fan
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hci : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hbi : InjOn beta (Icc 0 B))
    (hcreg : ∀ t ∈ Ioo 0 D, deriv base t ≠ 0)
    (hareg : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U)
    (v : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v.1 ≠ base 0) (hv1 : v.1 ≠ base D) (hvT : v.1 ≠ alpha A) :
    coordinateVertexAngleContribution g R.coordinates R.basis v.1 =
      if v.1 ∈ frontier U then Real.pi else 2 * Real.pi := by
  have hregular_fan {eta : ℝ → AnnulusCoordinates} {a b p : ℝ}
      (he : ContDiff ℝ ∞ eta) (hei : InjOn eta (Icc a b)) (hp : p ∈ Ioo a b)
      (hr : deriv eta p ≠ 0) {K : Set AnnulusCoordinates} (hK : IsCompact K)
      (hpK : eta p ∉ K) (hf : frontier U = eta '' Icc a b ∪ K)
      (hv : v.1 = eta p) :
      coordinateVertexAngleContribution g R.coordinates R.basis v.1 = Real.pi :=
    m64Intrinsic_region_arc_boundary_fan R.face R.coordinates R.basis R.smooth
      R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
      R.intersections R.intersection_frontier g he hei hp hr hK hpK
      hU hV hUV hf hfV R.cover v hv
  by_cases hvboundary : v.1 ∈ frontier U
  · rw [if_pos hvboundary]
    rw [hfront] at hvboundary
    rcases hvboundary with hvc | hva | hvb
    · obtain ⟨p, hp, hpv⟩ := hvc
      have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
        hv0 (hpv.symm.trans (congrArg base h.symm)))
      have hpD : p < D := lt_of_le_of_ne hp.2 (fun h =>
        hv1 (hpv.symm.trans (congrArg base h)))
      have hpK : base p ∉ alpha '' Icc 0 A ∪ beta '' Icc 0 B := by
        rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
        · exact hp0.ne' (hbaseA p hp t ht he.symm).1
        · exact hpD.ne (hbaseB p hp t ht he.symm).1
      exact hregular_fan hc hci ⟨hp0, hpD⟩ (hcreg p ⟨hp0, hpD⟩)
        ((isCompact_Icc.image ha.continuous).union (isCompact_Icc.image hb.continuous))
        hpK hfront hpv.symm
    · obtain ⟨p, hp, hpv⟩ := hva
      have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
        hv0 (hpv.symm.trans ((congrArg alpha h.symm).trans hstartA.symm)))
      have hpA : p < A := lt_of_le_of_ne hp.2 (fun h =>
        hvT (hpv.symm.trans (congrArg alpha h)))
      have hpK : alpha p ∉ base '' Icc 0 D ∪ beta '' Icc 0 B := by
        rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
        · exact hp0.ne' (hbaseA t ht p hp he).2
        · exact hpA.ne (hsides p hp t ht he.symm).1
      exact hregular_fan ha hai ⟨hp0, hpA⟩ (hareg p ⟨hp0, hpA⟩)
        ((isCompact_Icc.image hc.continuous).union (isCompact_Icc.image hb.continuous))
        hpK (hfront.trans (by ac_rfl)) hpv.symm
    · obtain ⟨p, hp, hpv⟩ := hvb
      have hp0 : 0 < p := lt_of_le_of_ne hp.1 (fun h =>
        hv1 (hpv.symm.trans ((congrArg beta h.symm).trans hstartB.symm)))
      have hpB : p < B := lt_of_le_of_ne hp.2 (fun h =>
        hvT (hpv.symm.trans ((congrArg beta h).trans hmeet.symm)))
      have hpK : beta p ∉ base '' Icc 0 D ∪ alpha '' Icc 0 A := by
        rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
        · exact hp0.ne' (hbaseB t ht p hp he).2
        · exact hpB.ne (hsides t ht p hp he).2
      exact hregular_fan hb hbi ⟨hp0, hpB⟩ (hbreg p ⟨hp0, hpB⟩)
        ((isCompact_Icc.image hc.continuous).union (isCompact_Icc.image ha.continuous))
        hpK (hfront.trans (by ac_rfl)) hpv.symm
  · rw [if_neg hvboundary]
    have htrace : frontier (⋃ i, (R.face i).carrier) = frontier U := by
      rw [R.cover, (m64Intrinsic_jordan_interior_closure hU hV hUV hfV.symm).2]
    have hvregion : v.1 ∈ ⋃ i, (R.face i).carrier := by
      obtain ⟨⟨i, k⟩, hik⟩ := v.2
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [R.carrier]
      exact ⟨R.basis i k, subset_convexHull ℝ _ (mem_range_self k), hik⟩
    have hvint : v.1 ∈ interior (⋃ i, (R.face i).carrier) := by
      by_contra h
      exact hvboundary (htrace ▸ ⟨subset_closure hvregion, h⟩)
    exact m64Intrinsic_regional_interior_vertex_fan R.face R.coordinates R.basis
      R.smooth R.inverse_smooth R.source R.carrier R.boundary R.boundary_injective
      R.intersections R.intersection_frontier g v hvint

end PoincareConjecture
