import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThinGraphBands

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_nested_graph_bands
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ} (hab : a < b)
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a b ua wa ub wb ra rb) :
    ∃ cutoff > 0, ∀ sa ∈ Ioo (0 : ℝ) cutoff, ∀ sb ∈ Ioo (0 : ℝ) cutoff,
      ∃ C : ObliqueBandFaces
        (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
        f a b ua wa ub wb sa sb,
        C.cuts.left = B.cuts.left ∧ C.cuts.right = B.cuts.right ∧
        (∀ q, C.coordinates q = B.coordinates q) ∧
        C.lowerArc = B.lowerArc ∧ C.band ⊆ B.band ∧ C.carrier ⊆ B.carrier ∧
        C.leftCut = segment ℝ (L (a, f a)) (L (a, f a) + sa • L (ua, wa)) ∧
        C.rightCut = segment ℝ (L (b, f b)) (L (b, f b) + sb • L (ub, wb)) := by
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num)) B.continuousOn_height
  obtain ⟨cutoff, hcutoff, hbands⟩ := m64Intrinsic_exists_thin_graph_bands L
    B.open_domain B.smooth_lower hab B.interval_subset B.cuts (B.height_pos ht)
  let S := B.cuts.linearCoordinates L B.open_domain B.smooth_lower
  have hBcoordinates (q : AnnulusCoordinates) : B.coordinates q = S (collarParameterEquiv q) := by
    change L (collarParameterEquiv (collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower (collarParameterEquiv q)))) = _
    rw [collarParameterEquiv.apply_symm_apply]
    rfl
  refine ⟨cutoff, hcutoff, ?_⟩
  intro sa hsa sb hsb
  obtain ⟨C, hleft, hright, hcoordinates, hheight, hcarrier, hcutA, hcutB⟩ :=
    hbands sa hsa sb hsb
  have hsame (q : AnnulusCoordinates) : C.coordinates q = B.coordinates q :=
    (hcoordinates q).trans (hBcoordinates q).symm
  have hband : C.band ⊆ B.band := by
    intro q hq
    rw [C.band_eq_subgraph] at hq
    rw [B.band_eq_subgraph]
    exact ⟨hq.1, hq.2.1,
      (hq.2.2.trans_lt (hheight _ hq.1)).le.trans (hmin hq.1)⟩
  refine ⟨C, hleft, hright, hsame, rfl, hband, ?_, hcutA, hcutB⟩
  rw [hcarrier, B.carrier_eq_image]
  rintro p ⟨q, hq, rfl⟩
  refine ⟨collarParameterEquiv.symm q, ?_, ?_⟩
  · rw [B.band_eq_subgraph]
    simp only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply]
    exact ⟨hq.1, hq.2.1, (hq.2.2.trans_lt (hheight q.1 hq.1)).le.trans (hmin hq.1)⟩
  · rw [hBcoordinates, collarParameterEquiv.apply_symm_apply]

end PoincareConjecture
