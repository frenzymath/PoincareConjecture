import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandEndpointGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem endpoint_one_mem_top
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F f a b ua wa ub wb ra rb) (right : Bool) :
    (B.endpointEdge right).map 1 ∈ B.polygonalTop := by
  rw [← B.height_graph_image]
  refine ⟨if right then 1 else 0, by cases right <;> simp, ?_⟩
  rw [B.endpointEdge_map]
  cases right <;> simp only [Bool.false_eq_true, if_false, if_true, one_mul] <;> rfl

private theorem cut_mem_open_edge
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F f a b ua wa ub wb ra rb) (right : Bool)
    {p z : AnnulusCoordinates} (hbase : (B.endpointEdge right).map 0 = p)
    (hz : z ∈ (B.endpointEdge right).map '' Icc (0 : ℝ) 1)
    (hzp : z ≠ p) (hzt : z ∉ B.polygonalTop) :
    z ∈ (B.endpointEdge right).map '' Ioo (0 : ℝ) 1 := by
  obtain ⟨s, hs, hsz⟩ := hz
  have hs0 : s ≠ 0 := fun h => hzp (hsz.symm.trans (h ▸ hbase))
  have hs1 : s ≠ 1 := fun h => hzt (hsz ▸ (h.symm ▸ endpoint_one_mem_top B right))
  exact ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩, hsz⟩

theorem m64Intrinsic_exists_matched_band_join_frontier_neighborhood
    {F F' : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f g : ℝ → ℝ} {a b ua wa ub wb ra rb a' b' ua' wa' ub' wb' ra' rb' : ℝ}
    (B : ObliqueBandFaces F f a b ua wa ub wb ra rb)
    (C : ObliqueBandFaces F' g a' b' ua' wa' ub' wb' ra' rb')
    (right right' : Bool) {p : AnnulusCoordinates}
    (hbase : (B.endpointEdge right).map 0 = p)
    (hbase' : (C.endpointEdge right').map 0 = p)
    (hcut : (B.endpointEdge right).map '' Icc (0 : ℝ) 1 =
      (C.endpointEdge right').map '' Icc (0 : ℝ) 1)
    (hinter : B.carrier ∩ C.carrier ⊆ frontier B.carrier) :
    ∃ N : Set AnnulusCoordinates, IsOpen N ∧ p ∈ N ∧
      N ∩ frontier (B.carrier ∪ C.carrier) ⊆ B.lowerArc ∪ C.lowerArc := by
  have hpB : p ∈ B.lowerArc := by
    rw [← hbase]
    exact (m64Intrinsic_band_endpoint_mem_lower_iff B right (by norm_num)).mpr rfl
  have hpC : p ∈ C.lowerArc := by
    rw [← hbase']
    exact (m64Intrinsic_band_endpoint_mem_lower_iff C right' (by norm_num)).mpr rfl
  obtain ⟨J, hJ, hpJ, hfrontB⟩ := m64Intrinsic_exists_band_endpoint_neighborhood B right
  obtain ⟨J', hJ', hpJ', hfrontC⟩ := m64Intrinsic_exists_band_endpoint_neighborhood C right'
  let N := (J ∩ J') ∩ (B.polygonalTop ∪ C.polygonalTop)ᶜ
  refine ⟨N, (hJ.inter hJ').inter
    (B.isCompact_polygonalTop.union C.isCompact_polygonalTop).isClosed.isOpen_compl,
    ⟨⟨hbase ▸ hpJ, hbase' ▸ hpJ'⟩, ?_⟩, ?_⟩
  · rintro (hz | hz)
    · exact disjoint_left.mp (m64Intrinsic_band_top_disjoint_lower B) hz hpB
    · exact disjoint_left.mp (m64Intrinsic_band_top_disjoint_lower C) hz hpC
  · intro z hz
    have hshared (hzc : z ∈ (B.endpointEdge right).map '' Icc (0 : ℝ) 1) :
        z ∈ B.lowerArc ∪ C.lowerArc := by
      by_cases hzp : z = p
      · exact Or.inl (hzp.symm ▸ hpB)
      have hzB := cut_mem_open_edge B right hbase hzc hzp (fun h => hz.1.2 (Or.inl h))
      have hzC := cut_mem_open_edge C right' hbase' (hcut ▸ hzc) hzp
        (fun h => hz.1.2 (Or.inr h))
      exact (hz.2.2 (B.shared_endpointCut_subset_interior_union C right right'
        hcut hinter ⟨hzB, hzC⟩)).elim
    rcases frontier_union_subset B.carrier C.carrier hz.2 with hf | hf
    · exact (hfrontB ⟨hz.1.1.1, hf.1⟩).elim Or.inl hshared
    · exact (hfrontC ⟨hz.1.1.2, hf.2⟩).elim Or.inr (fun h => hshared (hcut.symm ▸ h))

end PoincareConjecture
