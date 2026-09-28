import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcRegionTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MarkedRegionTriangulation





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_exists_digon_triangulation
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hareg : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hind0 : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U) (hcompact : IsCompact (closure U)) :
    ∃ R : M64IntrinsicCoordinateTriangulation (closure U),
      ∃ v0 v1 : Euler.CoordinateVertex R.coordinates R.basis,
        v0.1 = alpha 0 ∧ v1.1 = alpha A := by
  have hinter : alpha '' Icc 0 A ∩ beta '' Icc 0 B ⊆ {alpha 0, alpha A} := by
    rintro p ⟨⟨s, hs, hsp⟩, ⟨t, ht, htp⟩⟩
    rcases hmeet s hs t ht (hsp.trans htp.symm) with h | h
    · exact Or.inl (hsp.symm.trans (congrArg alpha h.1))
    · exact Or.inr (hsp.symm.trans (congrArg alpha h.1))
  obtain ⟨m, face, C, b, hC, hCi, hsource, hcarrier, hboundary, hfrontier,
      hcontacts, hcover, v0, v1, hv0, hv1⟩ :=
    m64Intrinsic_exists_two_arc_region_triangulation ha hb hA hB hai hbi hareg hbreg
      hinter hbase hend hind0 hind1 hU hV hUV hfront hfV hcompact
  exact ⟨⟨m, face, C, b, hC, hCi, hsource, hcarrier, hboundary,
    hfrontier, hcontacts, hcover⟩, v0, v1, hv0, hv1⟩

end PoincareConjecture
