import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCutContacts




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture




theorem m64Intrinsic_band_endpoint_cuts_disjoint
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F f a b ua wa ub wb ra rb) :
    Disjoint B.leftCut B.rightCut := by
  have hleft : B.leftCut = (B.endpointEdge false).map '' Icc (0 : ℝ) 1 :=
    (B.endpointEdge_image false).symm
  have hright : B.rightCut = (B.endpointEdge true).map '' Icc (0 : ℝ) 1 :=
    (B.endpointEdge_image true).symm
  rw [hleft, hright]
  apply disjoint_left.mpr
  rintro z ⟨s, hs, hsz⟩ ⟨t, ht, htz⟩
  have heq := hsz.trans htz.symm
  rw [B.endpointEdge_map, B.endpointEdge_map] at heq
  have hh0 : 0 < B.height 0 := B.height_pos (by norm_num)
  have hh1 : 0 < B.height 1 := B.height_pos (by norm_num)
  have hs' := m64Intrinsic_band_height_mem_source B (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (z := s * B.height 0)
    ⟨mul_nonneg hs.1 hh0.le, by nlinarith [hs.2]⟩
  have ht' := m64Intrinsic_band_height_mem_source B (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    (z := t * B.height 1)
    ⟨mul_nonneg ht.1 hh1.le, by nlinarith [ht.2]⟩
  have h := congrArg (fun q => (collarParameterEquiv q).1) (B.coordinates.injOn hs' ht' heq)
  norm_num only [collarParameterEquiv.apply_symm_apply, Prod.fst] at h





theorem m64Intrinsic_nested_patch_obstacle_contacts
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F f a b ua wa ub wb ra rb) (right : Bool)
    {K Z X Y Z' S T : Set AnnulusCoordinates}
    (hBZ : B.carrier ∩ Z ⊆ if right then B.leftCut else B.rightCut)
    (hK : Disjoint K (B.carrier ∪ Z)) (hY : Y ⊆ B.carrier) (hZ : Z' ⊆ Z)
    (hS : S ⊆ K) (hT : T ⊆ (if right then B.rightCut else B.leftCut) ∩ Y)
    (hcontact : (K ∪ (B.carrier ∪ Z)) ∩ X = S ∪ T) :
    K ∩ X = S ∧ Y ∩ X = T ∧ Disjoint Z' X := by
  have hcuts : Disjoint (if right then B.rightCut else B.leftCut)
      (if right then B.leftCut else B.rightCut) := by
    cases right
    · exact m64Intrinsic_band_endpoint_cuts_disjoint B
    · exact (m64Intrinsic_band_endpoint_cuts_disjoint B).symm
  have hSX : S ⊆ X := fun _ hs => (hcontact.symm.subset (Or.inl hs)).2
  have hTX : T ⊆ X := fun _ ht => (hcontact.symm.subset (Or.inr ht)).2
  refine ⟨subset_antisymm ?_ (subset_inter hS hSX),
    subset_antisymm ?_ (subset_inter (fun _ ht => (hT ht).2) hTX), ?_⟩
  · rintro z ⟨hzK, hzX⟩
    rcases hcontact.subset ⟨Or.inl hzK, hzX⟩ with hzS | hzT
    · exact hzS
    · exact (disjoint_left.mp hK hzK (Or.inl (hY (hT hzT).2))).elim
  · rintro z ⟨hzY, hzX⟩
    rcases hcontact.subset ⟨Or.inr (Or.inl (hY hzY)), hzX⟩ with hzS | hzT
    · exact (disjoint_left.mp hK (hS hzS) (Or.inl (hY hzY))).elim
    · exact hzT
  · apply disjoint_left.mpr
    intro z hzZ hzX
    rcases hcontact.subset ⟨Or.inr (Or.inr (hZ hzZ)), hzX⟩ with hzS | hzT
    · exact disjoint_left.mp hK (hS hzS) (Or.inr (hZ hzZ))
    · exact disjoint_left.mp hcuts (hT hzT).1 (hBZ ⟨hY (hT hzT).2, hZ hzZ⟩)

end PoincareConjecture
