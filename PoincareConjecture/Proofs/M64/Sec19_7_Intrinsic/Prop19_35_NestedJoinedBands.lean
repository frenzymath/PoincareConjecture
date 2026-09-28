import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedBandCutContact





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_exists_nested_joined_bands
    (L R : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f g : ℝ → ℝ} {a b c d ua wa ub wb uc wc ud wd ra r rb : ℝ}
    (hab : a < b) (hcd : c < d)
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a b ua wa ub wb ra r)
    (C : ObliqueBandFaces
      (collarParameterEquiv.trans R).toHomeomorph.toOpenPartialHomeomorph
      g c d uc wc ud wd r rb)
    {p w : AnnulusCoordinates}
    (hbaseB : L (b, f b) = p) (hbaseC : R (c, g c) = p)
    (hdirB : L (ub, wb) = w) (hdirC : R (uc, wc) = w)
    (hinter : B.carrier ∩ C.carrier = segment ℝ p (p + r • w)) :
    ∃ cutoff > 0, ∀ sa ∈ Ioo (0 : ℝ) cutoff, ∀ s ∈ Ioo (0 : ℝ) cutoff,
      ∀ sb ∈ Ioo (0 : ℝ) cutoff,
        ∃ (B' : ObliqueBandFaces
          (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
          f a b ua wa ub wb sa s)
          (C' : ObliqueBandFaces
          (collarParameterEquiv.trans R).toHomeomorph.toOpenPartialHomeomorph
          g c d uc wc ud wd s sb),
          (∀ q, B'.coordinates q = B.coordinates q) ∧
          (∀ q, C'.coordinates q = C.coordinates q) ∧
          B'.lowerArc = B.lowerArc ∧ C'.lowerArc = C.lowerArc ∧
          B'.band ⊆ B.band ∧ C'.band ⊆ C.band ∧
          B'.carrier ⊆ B.carrier ∧ C'.carrier ⊆ C.carrier ∧
          B'.carrier ∩ B.leftCut = B'.leftCut ∧
          C'.carrier ∩ C.rightCut = C'.rightCut ∧
          B'.rightCut = segment ℝ p (p + s • w) ∧
          C'.leftCut = segment ℝ p (p + s • w) ∧
          B'.carrier ∩ C'.carrier = segment ℝ p (p + s • w) := by
  obtain ⟨epsilonB, heB, hB⟩ := m64Intrinsic_exists_nested_graph_bands L hab B
  obtain ⟨epsilonC, heC, hC⟩ := m64Intrinsic_exists_nested_graph_bands R hcd C
  refine ⟨min epsilonB epsilonC, lt_min heB heC, ?_⟩
  intro sa hsa s hs sb hsb
  obtain ⟨B', _, _, hBc, hBl, hBb, hBk, _, hBr⟩ :=
    hB sa ⟨hsa.1, hsa.2.trans_le (min_le_left _ _)⟩
      s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
  obtain ⟨C', _, _, hCc, hCl, hCb, hCk, hCa, _⟩ :=
    hC s ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩
      sb ⟨hsb.1, hsb.2.trans_le (min_le_right _ _)⟩
  have hBright : B.rightCut = segment ℝ p (p + r • w) := by
    simpa only [hbaseB, hdirB] using m64Intrinsic_band_right_cut L B
  have hBright' : B'.rightCut = segment ℝ p (p + s • w) := by
    simpa only [hbaseB, hdirB] using hBr
  have hCleft' : C'.leftCut = segment ℝ p (p + s • w) := by
    simpa only [hbaseC, hdirC] using hCa
  have hcontact : B'.carrier ∩ B.rightCut = B'.rightCut :=
    m64Intrinsic_nested_band_cut_contact B B' hBc hBb true
  refine ⟨B', C', hBc, hCc, hBl, hCl, hBb, hCb, hBk, hCk,
    m64Intrinsic_nested_band_cut_contact B B' hBc hBb false,
    m64Intrinsic_nested_band_cut_contact C C' hCc hCb true, hBright', hCleft', ?_⟩
  apply subset_antisymm
  · intro z hz
    have hzold : z ∈ B.rightCut := hBright.symm ▸ hinter ▸ ⟨hBk hz.1, hCk hz.2⟩
    exact hBright' ▸ hcontact ▸ ⟨hz.1, hzold⟩
  · intro z hz
    constructor
    · apply B'.isClosed_carrier.frontier_subset
      apply B'.endpointEdge_subset_frontier true
      rw [B'.endpointEdge_image true]
      exact hBright'.symm ▸ hz
    · apply C'.isClosed_carrier.frontier_subset
      apply C'.endpointEdge_subset_frontier false
      rw [C'.endpointEdge_image false]
      exact hCleft'.symm ▸ hz

end PoincareConjecture
