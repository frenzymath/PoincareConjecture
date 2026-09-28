import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalHalfBands
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBoundaryCollarTopology
import PoincareConjecture.Proofs.M76.Mathlib.ClosedRegionPatchIncidence



set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem exists_coface_hull_of_mem_barycentricDualBlock
    (s : Finset E) {x : E} (hx : x ∈ (K.barycentricDualBlock s).space) :
    ∃ t ∈ K.faces, s ⊆ t ∧ x ∈ convexHull ℝ (t : Set E) := by
  obtain ⟨q, hq, hxq⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha, hfaces, hchain, heq⟩ :=
    (K.barycentricSubdivision_faces_of_face_chains q).mp hq.1
  obtain ⟨t, ht, hmax⟩ := a.exists_max_image Finset.card ha
  have hsub (u : Finset E) (hu : u ∈ a) : u ⊆ t := by
    rcases hchain u hu t ht with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hmax u hu)).symm.subset
  have hct : t.centroid ℝ id ∈ q := heq.symm ▸ Finset.mem_image.mpr ⟨t, ht, rfl⟩
  obtain ⟨v, hv, hsv, hvct⟩ := hq.2 _ hct
  have hvt : v = t := congrArg Subtype.val
    (K.faceCentroid_injective (show (⟨v, hv⟩ : K.faces).val.centroid ℝ id =
      (⟨t, hfaces t ht⟩ : K.faces).val.centroid ℝ id from hvct))
  refine ⟨t, hfaces t ht, hvt ▸ hsv, ?_⟩
  apply (convexHull_min ?_ (convex_convexHull ℝ _)) hxq
  intro z hz
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (heq ▸ hz)
  exact convexHull_mono (hsub u hu)
    (u.centroid_mem_convexHull (K.nonempty_of_mem_faces (hfaces u hu)))

theorem exists_original_coface_hull_of_barycentric_face
    {s q : Finset E} (hs : s ∈ K.faces) (hq : q ∈ K.barycentricSubdivision.faces)
    (hcent : s.centroid ℝ id ∈ q) :
    ∃ t ∈ K.faces, s ⊆ t ∧ convexHull ℝ (q : Set E) ⊆ convexHull ℝ (t : Set E) := by
  obtain ⟨a, ha, hfaces, hchain, heq⟩ :=
    (K.barycentricSubdivision_faces_of_face_chains q).mp hq
  obtain ⟨t, ht, hmax⟩ := a.exists_max_image Finset.card ha
  have hsub (u : Finset E) (hu : u ∈ a) : u ⊆ t := by
    rcases hchain u hu t ht with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hmax u hu)).symm.subset
  obtain ⟨v, hv, hvc⟩ := Finset.mem_image.mp (heq ▸ hcent)
  have hvs : v = s := congrArg Subtype.val
    (K.faceCentroid_injective (show (⟨v, hfaces v hv⟩ : K.faces).val.centroid ℝ id =
      (⟨s, hs⟩ : K.faces).val.centroid ℝ id from hvc))
  refine ⟨t, hfaces t ht, hvs ▸ hsub v hv, convexHull_min ?_ (convex_convexHull ℝ _)⟩
  intro z hz
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (heq ▸ hz)
  exact convexHull_mono (hsub u hu)
    (u.centroid_mem_convexHull (K.nonempty_of_mem_faces (hfaces u hu)))

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  [Fintype K.barycentricSubdivision.faces]

theorem residualBand_subset_original_cofaces
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (B : OriginalResidualHalfBands K e) :
    residualBand K e ⊆ convexHull ℝ ((B.coface 0).val : Set E) ∪
      convexHull ℝ ((B.coface 1).val : Set E) := by
  intro x hx
  obtain ⟨q, hq, hcq, hxq⟩ :=
    K.barycentricSubdivision.exists_coface_hull_of_mem_barycentricDualBlock
      {(originalEdgeCentroid K e).val} hx
  obtain ⟨t, ht, het, hqt⟩ := K.exists_original_coface_hull_of_barycentric_face
    e.property.1 hq (hcq (Finset.mem_singleton_self _))
  obtain ⟨u, hu, htu, huc⟩ := hpure t ht
  have hxu := convexHull_mono htu (hqt hxq)
  have hset : {v : Finset E | v ∈ K.faces ∧ v.card = 3 ∧
      e.val.map (Function.Embedding.subtype _) ⊆ v} =
      {(B.coface 0).val, (B.coface 1).val} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · rintro v (rfl | rfl)
      · exact ⟨(B.coface 0).property.1, (B.coface 0).property.2, B.edge_subset 0⟩
      · exact ⟨(B.coface 1).property.1, (B.coface 1).property.2, B.edge_subset 1⟩
    · rw [Set.ncard_pair (fun h ↦ B.coface_ne (Subtype.ext h)),
        hcofaces _ e.property.1 (by simpa using e.property.2)]
    · exact Set.toFinite _
  have humem := hset.subset ⟨hu, huc, het.trans htu⟩
  rcases humem with h | h
  · exact Or.inl (h ▸ hxu)
  · exact Or.inr (h ▸ hxu)

theorem residualBand_inter_original_edge
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    residualBand K e ∩ segment ℝ a.val b.val = residualBridge K e a b := by
  have hsplit : segment ℝ a.val b.val =
      segment ℝ (originalEdgeCentroid K e).val a.val ∪
        segment ℝ (originalEdgeCentroid K e).val b.val := by
    rw [originalEdgeCentroid_val K e heq, segment_eq_image_lineMap,
      segment_symm ℝ (AffineMap.lineMap a.val b.val (1 / 2 : ℝ)) a.val]
    have hleft : segment ℝ a.val (AffineMap.lineMap a.val b.val (1 / 2 : ℝ)) =
        AffineMap.lineMap a.val b.val '' Icc (0 : ℝ) (1 / 2) := by
      rw [← segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2),
        image_segment, AffineMap.lineMap_apply_zero]
    have hright : segment ℝ (AffineMap.lineMap a.val b.val (1 / 2 : ℝ)) b.val =
        AffineMap.lineMap a.val b.val '' Icc (1 / 2 : ℝ) 1 := by
      rw [← segment_eq_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1),
        image_segment, AffineMap.lineMap_apply_one]
    rw [hleft, hright, ← image_union]
    congr 1
    ext r
    simp only [mem_Icc, mem_union]
    constructor
    · intro h
      by_cases hr : r ≤ 1 / 2
      · exact Or.inl ⟨h.1, hr⟩
      · exact Or.inr ⟨le_of_not_ge hr, h.2⟩
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
  rw [hsplit, inter_union_distrib_left,
    (residualBand_halfEdge_passage K e a (by simp [heq])).1,
    (residualBand_halfEdge_passage K e b (by simp [heq])).1,
    ← residualBridge_eq_band_radii K e heq]

theorem OriginalResidualHalfBands.coface_hulls_inter
    {e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex}
    (B : OriginalResidualHalfBands K e) :
    convexHull ℝ ((B.coface 0).val : Set E) ∩
        convexHull ℝ ((B.coface 1).val : Set E) =
      convexHull ℝ (e.val.map (Function.Embedding.subtype _) : Set E) := by
  have hne : (B.coface 0).val ≠ (B.coface 1).val :=
    fun h ↦ B.coface_ne (Subtype.ext h)
  have hi : (B.coface 0).val ∩ (B.coface 1).val ≠ (B.coface 0).val := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le
      (h ▸ Finset.inter_subset_right) (by rw [(B.coface 0).property.2,
        (B.coface 1).property.2]))
  have hlt := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hi⟩)
  have heq : e.val.map (Function.Embedding.subtype _) =
      (B.coface 0).val ∩ (B.coface 1).val := by
    apply Finset.eq_of_subset_of_card_le
      (Finset.subset_inter (B.edge_subset 0) (B.edge_subset 1))
    rw [Finset.card_map, e.property.2]
    rw [(B.coface 0).property.2] at hlt
    omega
  rw [K.convexHull_inter_convexHull (B.coface 0).property.1 (B.coface 1).property.1,
    ← Finset.coe_inter, ← heq]

theorem residualCofaceContact_subset_original_coface
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3) :
    residualCofaceContact K e t ⊆ convexHull ℝ (t : Set E) := by
  intro x hx
  obtain ⟨q, hq, hcq, hxq⟩ :=
    K.barycentricSubdivision.exists_coface_hull_of_mem_barycentricDualBlock
      {(originalEdgeCentroid K e).val, t.centroid ℝ id} hx
  obtain ⟨u, hu, htu, hqu⟩ := K.exists_original_coface_hull_of_barycentric_face
    ht hq (hcq (by simp))
  have htu' : t = u := Finset.eq_of_subset_of_card_le htu (by rw [htc]; exact hbound u hu)
  exact htu'.symm ▸ hqu hxq



theorem OriginalResidualHalfBands.piece_subset_original_coface
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    {e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex}
    (B : OriginalResidualHalfBands K e) (i : Fin 2) :
    B.piece i ⊆ convexHull ℝ ((B.coface i).val : Set E) := by
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, htc⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq htc
  let bridge := residualBridge K e (B.ends 0) (B.ends 1)
  have hc := (B.disk i).isConnected_sdiff_of_subset_boundary
    (show bridge ⊆ B.outer i ∪ bridge from subset_union_right)
  have hclosure : closure (B.piece i \ bridge) = B.piece i :=
    (B.disk i).closure_sdiff_of_subset_boundary subset_union_right
  have hedge : convexHull ℝ (e.val.map (Function.Embedding.subtype _) : Set E) =
      segment ℝ (B.ends 0).val (B.ends 1).val := by
    simp only [B.edge_eq, Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype, Finset.coe_insert, Finset.coe_singleton, convexHull_pair]
  have hpair : Pairwise (fun j k : Fin 2 ↦
      convexHull ℝ ((B.coface j).val : Set E) ∩
        convexHull ℝ ((B.coface k).val : Set E) ⊆
          segment ℝ (B.ends 0).val (B.ends 1).val) := by
    intro j k hjk
    fin_cases j <;> fin_cases k
    · exact (hjk rfl).elim
    · exact (B.coface_hulls_inter K).trans hedge |>.subset
    · rw [inter_comm]
      exact (B.coface_hulls_inter K).trans hedge |>.subset
    · exact (hjk rfl).elim
  have hcover : B.piece i \ bridge ⊆ ⋃ j : Fin 2,
      convexHull ℝ ((B.coface j).val : Set E) := by
    intro x hx
    rcases residualBand_subset_original_cofaces K hpure hcofaces e B
      (B.piece_subset_band i hx.1) with h | h
    · exact mem_iUnion.mpr ⟨0, h⟩
    · exact mem_iUnion.mpr ⟨1, h⟩
  have havoid : Disjoint (B.piece i \ bridge)
      (segment ℝ (B.ends 0).val (B.ends 1).val) := by
    apply disjoint_left.mpr
    intro x hx he
    exact hx.2 ((residualBand_inter_original_edge K e B.edge_eq).subset
      ⟨B.piece_subset_band i hx.1, he⟩)
  obtain ⟨j, hj⟩ := hc.exists_closure_subset_of_finite_closed_cover
    (fun j : Fin 2 ↦ convexHull ℝ ((B.coface j).val : Set E))
    (fun j ↦ ((B.coface j).val.finite_toSet.isCompact_convexHull ℝ).isClosed)
    hcover hpair havoid
  rw [hclosure] at hj
  have hji : j = i := by
    by_contra hne
    obtain ⟨x, hx⟩ := (B.attachment_interval hbound hcofaces i).isConnected.nonempty
    have hxj := hj (B.attachment_subset_piece i hx)
    have hxi := residualCofaceContact_subset_original_coface K hbound e
      (B.coface i).property.1 (B.coface i).property.2 hx
    have hxe := hpair hne ⟨hxj, hxi⟩
    have hxb := (residualBand_inter_original_edge K e B.edge_eq).subset
      ⟨B.piece_subset_band i (B.attachment_subset_piece i hx), hxe⟩
    exact disjoint_left.mp (B.bridge_disjoint_attachment hbound i) hxb hx
  exact hji ▸ hj

end PoincareConjecture.M76.OriginalTriangleCopies
