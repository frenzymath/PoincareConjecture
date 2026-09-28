import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandEndpointGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_shared_band_join_frontier_neighborhood
    (L L' : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {lo lo' : ℝ → ℝ} {a b ua wa ub wb ra r a' b' ua' wa' ub' wb' rb' : ℝ}
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      lo a b ua wa ub wb ra r)
    (B' : ObliqueBandFaces
      (collarParameterEquiv.trans L').toHomeomorph.toOpenPartialHomeomorph
      lo' a' b' ua' wa' ub' wb' r rb')
    {p d : AnnulusCoordinates}
    (hbase : L (b, lo b) = p) (hbase' : L' (a', lo' a') = p)
    (hdir : L (ub, wb) = d) (hdir' : L' (ua', wa') = d)
    (hinter : B.carrier ∩ B'.carrier = segment ℝ p (p + r • d)) :
    ∃ N : Set AnnulusCoordinates, IsOpen N ∧ p ∈ N ∧
      N ∩ frontier (B.carrier ∪ B'.carrier) ⊆ B.lowerArc ∪ B'.lowerArc := by
  have hcut : B.rightCut = segment ℝ p (p + r • d) := by
    simpa only [hbase, hdir] using m64Intrinsic_band_right_cut L B
  have hcut' : B'.leftCut = segment ℝ p (p + r • d) := by
    simpa only [hbase', hdir'] using m64Intrinsic_band_left_cut L' B'
  have hzero : (B.endpointEdge true).map 0 = p := by
    rw [m64Intrinsic_band_right_endpoint_zero]
    exact hbase
  have hzero' : (B'.endpointEdge false).map 0 = p := by
    rw [m64Intrinsic_band_left_endpoint_zero]
    exact hbase'
  have hpLower : p ∈ B.lowerArc := by
    rw [← hzero]
    exact (m64Intrinsic_band_endpoint_mem_lower_iff B true (by norm_num)).mpr rfl
  have hpTop : p ∉ B.polygonalTop := fun hp =>
    disjoint_left.mp (m64Intrinsic_band_top_disjoint_lower B) hp hpLower
  obtain ⟨J, hJ, hpJ, hfront⟩ := m64Intrinsic_exists_band_endpoint_neighborhood B true
  obtain ⟨J', hJ', hpJ', hfront'⟩ := m64Intrinsic_exists_band_endpoint_neighborhood B' false
  have hcancel := m64Intrinsic_band_shared_cut_interior L L' B B'
    hbase hbase' hdir hdir' hcut hcut' hinter
  have htip : p + r • d ∈ B.polygonalTop := by
    simpa only [hbase, hdir] using m64Intrinsic_band_right_tip_mem_top L B
  let N := (J ∩ J') ∩ B.polygonalTopᶜ
  refine ⟨N, (hJ.inter hJ').inter B.isCompact_polygonalTop.isClosed.isOpen_compl,
    ⟨⟨hzero ▸ hpJ, hzero' ▸ hpJ'⟩, hpTop⟩, ?_⟩
  intro z hz
  have hshared (hzc : z ∈ segment ℝ p (p + r • d)) :
      z ∈ B.lowerArc ∪ B'.lowerArc := by
    rw [← m64Intrinsic_ray_image_eq_segment p d B.right_length_pos.le] at hzc
    obtain ⟨s, hs, hsz⟩ := hzc
    by_cases hs0 : s = 0
    · have hpz : p = z := by simpa only [hs0, zero_smul, add_zero] using hsz
      exact Or.inl (hpz ▸ hpLower)
    by_cases hsr : s = r
    · have htz : p + r • d = z := by simpa only [hsr] using hsz
      exact False.elim (hz.1.2 (htz ▸ htip))
    exact False.elim (hz.2.2 (hcancel ⟨s,
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hsr⟩, hsz⟩))
  rcases frontier_union_subset B.carrier B'.carrier hz.2 with hf | hf
  · rcases hfront ⟨hz.1.1.1, hf.1⟩ with hlower | hsharedCut
    · exact Or.inl hlower
    · apply hshared
      simpa only [B.endpointEdge_image, ↓reduceIte, hcut] using hsharedCut
  · rcases hfront' ⟨hz.1.1.2, hf.2⟩ with hlower | hsharedCut
    · exact Or.inr hlower
    · apply hshared
      simpa only [B'.endpointEdge_image, Bool.false_eq_true, ↓reduceIte, hcut'] using hsharedCut

end PoincareConjecture
