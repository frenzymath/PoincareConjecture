import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.TreeCotreePartition
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ResidualBandCut
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.TreeSourceGeometry

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]

noncomputable def complementaryOriginalEdge (P : SimpleGraph K.vertices)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (s : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet) :
    Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex :=
  (complementaryTriangleEdgeEquiv K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
    (originalTriangleCofaceCounts K hcofaces) s).val

theorem complementaryOriginalEdge_coface_mem
    (P : SimpleGraph K.vertices)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (s : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (t : Triangle K)
    (het : (complementaryOriginalEdge K P hcofaces s).val.map (Function.Embedding.subtype _) ⊆ t.val) :
    (K.vertexFaceEquiv 3).symm t ∈ s.val := by
  classical
  have hsub : (complementaryOriginalEdge K P hcofaces s).val ⊆
      ((K.vertexFaceEquiv 3).symm t).val := by
    apply Finset.map_subset_map.mp
    rw [K.vertexFaceEquiv_symm_map]
    exact het
  have hmem : (K.vertexFaceEquiv 3).symm t ∈ triangleCofaces
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex (complementaryOriginalEdge K P hcofaces s) := by
    simp only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsub
  rw [complementaryOriginalEdge, complementaryTriangleEdgeEquiv_cofaces] at hmem
  letI : DecidableEq K.vertices := fun a b => Classical.propDecidable (a = b)
  exact Sym2.mem_toFinset.mp hmem

theorem complementaryCentroid_triangle_val
    (P : SimpleGraph K.vertices)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (t : Triangle K) :
    (complementaryCentroidEmbedding K P hcofaces (Sum.inl ((K.vertexFaceEquiv 3).symm t))).val =
      t.val.centroid ℝ id := by
  change (((K.vertexFaceEquiv 3).symm t).val.map (Function.Embedding.subtype _)).centroid ℝ id = _
  rw [K.vertexFaceEquiv_symm_map]

theorem residualCofaceContact_subset_selectedDualRim [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (s : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet) (t : Triangle K)
    (het : (complementaryOriginalEdge K P hcofaces s).val.map (Function.Embedding.subtype _) ⊆ t.val) :
    residualCofaceContact K (complementaryOriginalEdge K P hcofaces s) t.val ⊆
      K.barycentricSubdivision.vertexDualRim (selectedDualCentroidSet K P D hD hcofaces) := by
  let r := complementaryCentroidEmbedding K P hcofaces
  let q := (K.vertexFaceEquiv 3).symm t
  have hq : r (Sum.inl q) ∈ selectedDualCentroidSet K P D hD hcofaces := ⟨Sum.inl q, rfl⟩
  have hout : r (Sum.inr s) ∉ selectedDualCentroidSet K P D hD hcofaces :=
    complementary_edge_vertex_not_selected P D hD r rfl s hs
  have h := PoincareConjecture.M76.vertexDualRim_contains_selected_unselected_block
    (K := K.barycentricSubdivision) (p := r (Sum.inl q)) (q := r (Sum.inr s)) hq hout
  have htval : (r (Sum.inl q)).val = t.val.centroid ℝ id := complementaryCentroid_triangle_val K P hcofaces t
  have heval : r (Sum.inr s) = originalEdgeCentroid K (complementaryOriginalEdge K P hcofaces s) := rfl
  rw [htval, heval] at h
  unfold residualCofaceContact
  convert h using 1
  congr 2
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem residualBand_inter_selectedDual_two_contacts [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (s : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet) (t u : Triangle K) (htu : t ≠ u)
    (het : (complementaryOriginalEdge K P hcofaces s).val.map (Function.Embedding.subtype _) ⊆ t.val)
    (heu : (complementaryOriginalEdge K P hcofaces s).val.map (Function.Embedding.subtype _) ⊆ u.val) :
    residualBand K (complementaryOriginalEdge K P hcofaces s) ∩
      K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces) =
      residualCofaceContact K (complementaryOriginalEdge K P hcofaces s) t.val ∪
        residualCofaceContact K (complementaryOriginalEdge K P hcofaces s) u.val := by
  let r := complementaryCentroidEmbedding K P hcofaces
  let e := complementaryOriginalEdge K P hcofaces s
  have hinv := two_cofaces_inventory K (hcofaces _ e.property.1 (by
    rw [Finset.card_map]; exact e.property.2)) htu het heu
  have hmain := residualCentroidBlock_inter_selectedDual K P D hD hcofaces s hs
  change residualBand K e ∩ _ = _ at hmain
  rw [hmain]
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
    let qK : Triangle K := K.vertexFaceEquiv 3 q
    have heq : e.val.map (Function.Embedding.subtype _) ⊆ qK.val :=
      Finset.map_subset_map.mpr (complementaryTriangleEdgeEquiv_subset
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
        (originalTriangleCofaceCounts K hcofaces) s q hq)
    have hval : (r (Sum.inl q)).val = qK.val.centroid ℝ id := rfl
    change x ∈ (K.barycentricSubdivision.barycentricDualBlock
      {(originalEdgeCentroid K e).val, (r (Sum.inl q)).val}).space at hxq
    rw [hval] at hxq
    rcases (hinv qK).mp heq with hqt | hqu
    · left
      change x ∈ (K.barycentricSubdivision.barycentricDualBlock {(originalEdgeCentroid K e).val, _}).space
      simpa only [hqt] using hxq
    · right
      change x ∈ (K.barycentricSubdivision.barycentricDualBlock {(originalEdgeCentroid K e).val, _}).space
      simpa only [hqu] using hxq
  · rintro (hx | hx)
    · refine mem_iUnion₂.mpr ⟨(K.vertexFaceEquiv 3).symm t,
        complementaryOriginalEdge_coface_mem K P hcofaces s t het, ?_⟩
      change x ∈ (K.barycentricSubdivision.barycentricDualBlock
        {(originalEdgeCentroid K e).val,
          (complementaryCentroidEmbedding K P hcofaces (Sum.inl ((K.vertexFaceEquiv 3).symm t))).val}).space
      rw [complementaryCentroid_triangle_val]
      exact hx
    · refine mem_iUnion₂.mpr ⟨(K.vertexFaceEquiv 3).symm u,
        complementaryOriginalEdge_coface_mem K P hcofaces s u heu, ?_⟩
      change x ∈ (K.barycentricSubdivision.barycentricDualBlock
        {(originalEdgeCentroid K e).val,
          (complementaryCentroidEmbedding K P hcofaces (Sum.inl ((K.vertexFaceEquiv 3).symm u))).val}).space
      rw [complementaryCentroid_triangle_val]
      exact hx

end PoincareConjecture.M76.OriginalTriangleCopies
