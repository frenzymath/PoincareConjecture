import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalTreeNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTriangleOwnerIntervals

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]

theorem originalTriangleCofaceCounts
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    (triangleCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex e).card = 2 := by
  rw [K.triangleCofaces_card_eq_original e]
  apply hcofaces _ e.property.1
  simpa only [Finset.card_map] using e.property.2

noncomputable def complementaryCentroidEmbedding
    (P : SimpleGraph K.vertices)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph :=
  (dualFaceGraphEmbedding K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
    (originalTriangleCofaceCounts K hcofaces)).trans K.vertexFaceCentroidGraphIso.toEmbedding

noncomputable def selectedDualCentroidEmbedding
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    D.incidenceSubdivision ↪g K.barycentricSubdivision.vertexAbstractComplex.edgeGraph :=
  (PoincareConjecture.M76.dualIncidenceRestriction K.vertexAbstractComplex P D hD).trans
    (complementaryCentroidEmbedding K P hcofaces)

noncomputable def selectedDualCentroidSet
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    Set K.barycentricSubdivision.vertices :=
  Set.range (selectedDualCentroidEmbedding K P D hD hcofaces)

noncomputable def residualCentroidSet
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    Set K.barycentricSubdivision.vertices :=
  {z | ∃ s : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet,
    s.val ∉ D.edgeSet ∧ complementaryCentroidEmbedding K P hcofaces (Sum.inr s) = z}

theorem complementaryCentroid_range_eq_selected_union_residual
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    Set.range (complementaryCentroidEmbedding K P hcofaces) =
      selectedDualCentroidSet K P D hD hcofaces ∪ residualCentroidSet K P D hcofaces := by
  classical
  ext z
  constructor
  · rintro ⟨q | s, rfl⟩
    · exact Or.inl ⟨Sum.inl q, rfl⟩
    · by_cases hs : s.val ∈ D.edgeSet
      · exact Or.inl ⟨Sum.inr ⟨s.val, hs⟩, rfl⟩
      · exact Or.inr ⟨s, hs, rfl⟩
  · rintro (⟨x, rfl⟩ | ⟨s, _, rfl⟩)
    · exact ⟨PoincareConjecture.M76.dualIncidenceRestriction K.vertexAbstractComplex P D hD x, rfl⟩
    · exact ⟨Sum.inr s, rfl⟩

theorem complementaryCentroid_range_eq_compl_primal
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    Set.range (complementaryCentroidEmbedding K P hcofaces) =
      (primalCentroidSet K P hP)ᶜ := by
  have hsize (s : Finset K.vertices) (hs : s ∈ K.vertexAbstractComplex.faces) : s.card ≤ 3 := by
    simpa only [Finset.card_map] using hbound (s.map (Function.Embedding.subtype _)) hs
  change Set.range (K.vertexFaceCentroidGraphIso.toEquiv ∘
      dualFaceLabel K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
        (originalTriangleCofaceCounts K hcofaces)) =
    (Set.range (K.vertexFaceCentroidGraphIso.toEquiv ∘
      K.vertexAbstractComplex.primalFaceLabel P hP))ᶜ
  rw [Set.range_comp, Set.range_comp,
    K.vertexAbstractComplex.range_dualFaceLabel_eq_compl P hP
      (originalTriangleCofaceCounts K hcofaces) hsize]
  exact K.vertexFaceCentroidGraphIso.toEquiv.image_compl _

theorem treeCotree_centroid_partition
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    primalCentroidSet K P hP ∪ selectedDualCentroidSet K P D hD hcofaces ∪
      residualCentroidSet K P D hcofaces = Set.univ := by
  rw [Set.union_assoc, ← complementaryCentroid_range_eq_selected_union_residual K P D hD hcofaces,
    complementaryCentroid_range_eq_compl_primal K P hP hbound hcofaces]
  exact Set.union_compl_self _

theorem treeCotree_block_cover [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ∪
      K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces) ∪
      K.barycentricSubdivision.vertexDualUnion (residualCentroidSet K P D hcofaces) = K.space := by
  rw [← K.barycentricSubdivision.vertexDualUnion_union,
    ← K.barycentricSubdivision.vertexDualUnion_union,
    treeCotree_centroid_partition K P hP D hD hbound hcofaces,
    K.barycentricSubdivision.vertexDualUnion_univ, K.barycentricSubdivision_isSubdivision.space_eq]

theorem centroidBlock_inter_union [Fintype K.barycentricSubdivision.faces]
    (S : Set K.barycentricSubdivision.vertices) (p : K.barycentricSubdivision.vertices) :
    (K.barycentricSubdivision.barycentricDualBlock {p.val}).space ∩
      K.barycentricSubdivision.vertexDualUnion S =
        ⋃ q ∈ S, (K.barycentricSubdivision.barycentricDualBlock {p.val, q.val}).space := by
  ext x
  simp only [Geometry.SimplicialComplex.vertexDualUnion, mem_inter_iff, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hp, q, hq, hxq⟩
    exact ⟨q, hq, (K.barycentricSubdivision.vertex_dualBlocks_space_inter p.val q.val).subset ⟨hp, hxq⟩⟩
  · rintro ⟨q, hq, hx⟩
    have hh := (K.barycentricSubdivision.vertex_dualBlocks_space_inter p.val q.val).symm.subset hx
    exact ⟨hh.1, q, hq, hh.2⟩

theorem residualCentroidBlock_isFinitePLBallPair [Fintype K.barycentricSubdivision.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (p : K.barycentricSubdivision.vertices) :
    IsFinitePLBallPair (ℝ × ℝ)
      (K.barycentricSubdivision.barycentricDualBlock {p.val}).space
      (K.barycentricSubdivision.barycentricSubdivision.link p.val).space := by
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, ht⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hpure' : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hc⟩ := hpure s hs
    exact ⟨t, ht, hc, hst⟩
  exact K.barycentricSubdivision.isFinitePLBallPair_barycentricDualBlock_vertex
    (K.barycentricSubdivision_pure_triangles hpure')
    (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces) p.property
    (K.isConnected_barycentric_vertex_link_of_pure_triangles hpure'
      (fun q hq ↦ by simpa only [K.faceLink_singleton_eq_link] using hlinks q hq) p.property)

theorem centroidBlocks_adj_of_mem [Fintype K.barycentricSubdivision.faces]
    {p q : K.barycentricSubdivision.vertices} (hpq : p ≠ q) {x : E}
    (hp : x ∈ (K.barycentricSubdivision.barycentricDualBlock {p.val}).space)
    (hq : x ∈ (K.barycentricSubdivision.barycentricDualBlock {q.val}).space) :
    K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.Adj p q := by
  have hface : ({p.val, q.val} : Finset E) ∈ K.barycentricSubdivision.faces := by
    by_contra h
    have hx := (K.barycentricSubdivision.vertex_dualBlocks_space_inter p.val q.val).subset ⟨hp, hq⟩
    rw [K.barycentricSubdivision.barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.insert_nonempty _ _) h] at hx
    exact hx
  refine ⟨hpq, ?_⟩
  change (({p, q} : Finset K.barycentricSubdivision.vertices).map
    (Function.Embedding.subtype _)) ∈ K.barycentricSubdivision.faces
  simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hface

theorem edgeCentroidBlock_inter_primal [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ¬ edgeInGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P e) :
    (K.barycentricSubdivision.barycentricDualBlock {(originalEdgeCentroid K e).val}).space ∩
      K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) =
      ⋃ v ∈ e.val, primalEdgeContact K e v := by
  ext x
  constructor
  · rintro ⟨hx, hxP⟩
    obtain ⟨p, ⟨q, rfl⟩, hxp⟩ := mem_iUnion₂.mp hxP
    rcases q with v | f
    · have hne : originalVertexCentroid K v ≠ originalEdgeCentroid K e := by
        intro h
        exact originalEdgeCentroid_not_mem_primalCentroidSet K P hP e he
          (h ▸ originalVertexCentroid_mem_primalCentroidSet K P hP v)
      have ha := centroidBlocks_adj_of_mem K hne hxp hx
      have ha' := K.vertexFaceCentroidGraphIso.map_rel_iff.mp ha
      have hv : v ∈ e.val := by
        have hinc := (K.vertexAbstractComplex.toPreAbstractSimplicialComplex.faceInclusionGraph_adj_iff_of_card_lt
          ⟨{v}, K.vertexAbstractComplex.singleton_mem v⟩ ⟨e.val, e.property.1⟩ (by
            change ({v} : Finset K.vertices).card < e.val.card
            rw [Finset.card_singleton, e.property.2]
            omega)).mp ha'
        exact Finset.singleton_subset_iff.mp hinc
      exact mem_iUnion₂.mpr ⟨v, hv,
        (K.barycentricSubdivision.vertex_dualBlocks_space_inter
          (originalVertexCentroid K v).val (originalEdgeCentroid K e).val).subset ⟨hxp, hx⟩⟩
    · let fl := K.vertexAbstractComplex.primalFaceLabel P hP (Sum.inr f)
      have hne : fl ≠ (⟨e.val, e.property.1⟩ : K.vertexAbstractComplex.faces) := by
        intro h
        apply originalEdgeCentroid_not_mem_primalCentroidSet K P hP e he
        exact ⟨Sum.inr f, congrArg K.vertexFaceCentroidGraphIso h⟩
      have hc : fl.val.card = e.val.card :=
        (K.vertexAbstractComplex.primalFaceLabel_edge_card P hP f).trans e.property.2.symm
      exact (Set.disjoint_left.mp (sameCard_centroid_dualBlocks_disjoint K fl _ hne hc) hxp hx).elim
  · intro hx
    obtain ⟨v, _, hxv⟩ := mem_iUnion₂.mp hx
    have hh := (K.barycentricSubdivision.vertex_dualBlocks_space_inter
      (originalVertexCentroid K v).val (originalEdgeCentroid K e).val).symm.subset hxv
    exact ⟨hh.2, mem_iUnion₂.mpr ⟨originalVertexCentroid K v,
      originalVertexCentroid_mem_primalCentroidSet K P hP v, hh.1⟩⟩

theorem selectedDualCentroid_isFinitePLBallPair [Fintype K.barycentricSubdivision.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hDtree : D.IsTree) :
    IsFinitePLBallPair (ℝ × ℝ)
      (K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces))
      (K.barycentricSubdivision.vertexDualRim (selectedDualCentroidSet K P D hD hcofaces)) := by
  classical
  have hfinite : (selectedDualCentroidSet K P D hD hcofaces).Finite :=
    Set.finite_range (selectedDualCentroidEmbedding K P D hD hcofaces)
  let S := hfinite.toFinset
  have hS : (S : Set K.barycentricSubdivision.vertices) = selectedDualCentroidSet K P D hD hcofaces :=
    hfinite.coe_toFinset
  have htree : (K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
      (S : Set K.barycentricSubdivision.vertices)).IsTree := by
    rw [hS]
    exact (selectedDualCentroidEmbedding K P D hD hcofaces).isoInduceRange.isTree_iff.mp
      (SimpleGraph.IsTree.incidenceSubdivision D hDtree)
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, ht⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hpure' : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hc⟩ := hpure s hs
    exact ⟨t, ht, hc, hst⟩
  have hball := K.barycentricSubdivision.isFinitePLBallPair_vertexDualUnion_of_induced_tree
    (K.barycentricSubdivision_pure_triangles hpure')
    (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces)
    (fun p hp => K.isConnected_barycentric_vertex_link_of_pure_triangles hpure'
      (fun q hq => by simpa only [K.faceLink_singleton_eq_link] using hlinks q hq) hp)
    S htree
  rwa [hS] at hball

theorem residualCentroidBlock_inter_selectedDual [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (s : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet) :
    let r := complementaryCentroidEmbedding K P hcofaces
    (K.barycentricSubdivision.barycentricDualBlock {(r (Sum.inr s)).val}).space ∩
      K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces) =
      ⋃ q ∈ s.val, (K.barycentricSubdivision.barycentricDualBlock
        {(r (Sum.inr s)).val, (r (Sum.inl q)).val}).space := by
  intro r
  have hout : r (Sum.inr s) ∉ selectedDualCentroidSet K P D hD hcofaces :=
    complementary_edge_vertex_not_selected P D hD r rfl s hs
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    obtain ⟨p, ⟨q, rfl⟩, hxp⟩ := mem_iUnion₂.mp hxD
    have hne : r (Sum.inr s) ≠ selectedDualCentroidEmbedding K P D hD hcofaces q := by
      intro h
      exact hout (h ▸ (show selectedDualCentroidEmbedding K P D hD hcofaces q ∈
        selectedDualCentroidSet K P D hD hcofaces from ⟨q, rfl⟩))
    have ha := centroidBlocks_adj_of_mem K hne hx hxp
    have ha' : (complementaryTriangleGraph
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision.Adj
        (Sum.inr s) (PoincareConjecture.M76.dualIncidenceRestriction K.vertexAbstractComplex P D hD q) :=
      r.map_rel_iff.mp ha
    rcases q with q | f
    · exact mem_iUnion₂.mpr ⟨q, ha',
        (K.barycentricSubdivision.vertex_dualBlocks_space_inter
          (r (Sum.inr s)).val (r (Sum.inl q)).val).subset ⟨hx, hxp⟩⟩
    · exact ha'.elim
  · intro hx
    obtain ⟨q, _, hxq⟩ := mem_iUnion₂.mp hx
    have hh := (K.barycentricSubdivision.vertex_dualBlocks_space_inter
      (r (Sum.inr s)).val (r (Sum.inl q)).val).symm.subset hxq
    exact ⟨hh.1, mem_iUnion₂.mpr ⟨r (Sum.inl q), ⟨Sum.inl q, rfl⟩, hh.2⟩⟩

theorem selectedDual_disjoint_residual_centroids
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    Disjoint (selectedDualCentroidSet K P D hD hcofaces) (residualCentroidSet K P D hcofaces) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨q, hq⟩ ⟨s, hs, rfl⟩
  have hh := (complementaryCentroidEmbedding K P hcofaces).injective hq
  rcases q with q | f
  · cases hh
  · have hh' : f.val = s.val := congrArg (fun x :
        (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet ↦ x.val)
        (Sum.inr.inj hh)
    exact hs (hh' ▸ f.property)

theorem distinctComplementaryCentroidBlocks_disjoint [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (s t : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hst : s ≠ t) :
    Disjoint
      (K.barycentricSubdivision.barycentricDualBlock
        {(complementaryCentroidEmbedding K P hcofaces (Sum.inr s)).val}).space
      (K.barycentricSubdivision.barycentricDualBlock
        {(complementaryCentroidEmbedding K P hcofaces (Sum.inr t)).val}).space := by
  let counts := originalTriangleCofaceCounts K hcofaces
  apply sameCard_centroid_dualBlocks_disjoint K
    (dualFaceLabel K.vertexAbstractComplex.toPreAbstractSimplicialComplex P counts (Sum.inr s))
    (dualFaceLabel K.vertexAbstractComplex.toPreAbstractSimplicialComplex P counts (Sum.inr t))
  · intro h
    exact hst (Sum.inr.inj (dualFaceLabel_injective
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P counts h))
  · rw [dualFaceLabel_edge_card, dualFaceLabel_edge_card]

theorem treeCotree_exterior_eq_complementary_union [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces) ∪
      K.barycentricSubdivision.vertexDualUnion (residualCentroidSet K P D hcofaces) =
      K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)ᶜ := by
  rw [← K.barycentricSubdivision.vertexDualUnion_union,
    ← complementaryCentroid_range_eq_selected_union_residual K P D hD hcofaces,
    complementaryCentroid_range_eq_compl_primal K P hP hbound hcofaces]

theorem treeCotree_exterior_inter_primal [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ∩
      (K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces) ∪
        K.barycentricSubdivision.vertexDualUnion (residualCentroidSet K P D hcofaces)) =
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) := by
  rw [treeCotree_exterior_eq_complementary_union K P hP D hD hbound hcofaces]
  rfl

theorem exists_finite_triangulation_centroidUnion [Fintype K.barycentricSubdivision.faces]
    (S : Set K.barycentricSubdivision.vertices) :
    ∃ C : SimplicialComplex ℝ E, C.faces.Finite ∧
      C.space = K.barycentricSubdivision.vertexDualUnion S := by
  classical
  let : Finite K.barycentricSubdivision.vertices :=
    (K.barycentricSubdivision.finite_vertices_of_finite_faces (Set.toFinite _)).to_subtype
  let blocks : S → SimplicialComplex ℝ E :=
    fun p ↦ K.barycentricSubdivision.barycentricDualBlock {p.val.val}
  obtain ⟨C, hC, hCs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion blocks
    (fun p ↦ K.barycentricSubdivision.barycentricDualBlock_finite {p.val.val})
  refine ⟨C, hC, hCs.trans ?_⟩
  ext x
  simp only [Geometry.SimplicialComplex.vertexDualUnion, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.val, p.property, hp⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨⟨p, hp⟩, hx⟩

end PoincareConjecture.M76.OriginalTriangleCopies
