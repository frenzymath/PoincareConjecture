import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusLeafCutDisk
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComplementaryFaceColors
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SurfaceDualEdgeGeometry

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

noncomputable def primalCentroidEmbedding (P : SimpleGraph K.vertices)
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph) :
    P.incidenceSubdivision ↪g K.barycentricSubdivision.vertexAbstractComplex.edgeGraph :=
  (K.vertexAbstractComplex.primalFaceGraphEmbedding P hP).trans
    K.vertexFaceCentroidGraphIso.toEmbedding

noncomputable def primalCentroidSet (P : SimpleGraph K.vertices)
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph) : Set K.barycentricSubdivision.vertices :=
  Set.range (primalCentroidEmbedding K P hP)

noncomputable def originalVertexCentroid (v : K.vertices) :
    K.barycentricSubdivision.vertices :=
  K.vertexFaceCentroidGraphIso ⟨{v}, K.vertexAbstractComplex.singleton_mem v⟩

noncomputable def originalEdgeCentroid
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    K.barycentricSubdivision.vertices :=
  K.vertexFaceCentroidGraphIso ⟨e.val, e.property.1⟩

theorem originalVertexCentroid_mem_primalCentroidSet
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (v : K.vertices) : originalVertexCentroid K v ∈ primalCentroidSet K P hP :=
  ⟨Sum.inl v, rfl⟩

theorem originalEdgeCentroid_not_mem_primalCentroidSet
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ¬ edgeInGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P e) :
    originalEdgeCentroid K e ∉ primalCentroidSet K P hP := by
  rintro ⟨x, hx⟩
  have hx' : K.vertexAbstractComplex.primalFaceLabel P hP x = ⟨e.val, e.property.1⟩ :=
    K.vertexFaceCentroidGraphIso.injective hx
  have hmem : (⟨e.val, e.property.1⟩ : K.vertexAbstractComplex.faces) ∈
      Set.range (K.vertexAbstractComplex.primalFaceLabel P hP) := ⟨x, hx'⟩
  rcases (K.vertexAbstractComplex.mem_range_primalFaceLabel_iff P hP _).mp hmem with
    hcard | ⟨f, hf, hef⟩
  · have hc := e.property.2
    change e.val.card = 1 at hcard
    omega
  · exact he ((Subtype.ext hef : e = f).symm ▸ hf)

theorem originalVertexCentroid_adj_edgeCentroid
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val) :
    K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.Adj
      (originalVertexCentroid K v) (originalEdgeCentroid K e) := by
  apply K.vertexFaceCentroidGraphIso.map_rel_iff.mpr
  apply (K.vertexAbstractComplex.toPreAbstractSimplicialComplex.faceInclusionGraph_adj_iff_of_card_lt
    ⟨{v}, K.vertexAbstractComplex.singleton_mem v⟩ ⟨e.val, e.property.1⟩ ?_).mpr
  · exact Finset.singleton_subset_iff.mpr hv
  · change ({v} : Finset K.vertices).card < e.val.card
    rw [Finset.card_singleton, e.property.2]
    omega

theorem primalTreeNeighborhood_isFinitePLBallPair [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hPtree : P.IsTree) :
    IsFinitePLBallPair (ℝ × ℝ)
      (K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP))
      (K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP)) := by
  classical
  have hfinite : (primalCentroidSet K P hP).Finite :=
    Set.finite_range (primalCentroidEmbedding K P hP)
  let S := hfinite.toFinset
  have hS : (S : Set K.barycentricSubdivision.vertices) = primalCentroidSet K P hP :=
    hfinite.coe_toFinset
  have htree : (K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
      (S : Set K.barycentricSubdivision.vertices)).IsTree := by
    rw [hS]
    exact (SimpleGraph.Embedding.isoInduceRange (primalCentroidEmbedding K P hP)).isTree_iff.mp
      (SimpleGraph.IsTree.incidenceSubdivision P hPtree)
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

noncomputable def primalEdgeContact [Fintype K.barycentricSubdivision.faces]
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) : Set E :=
  (K.barycentricSubdivision.barycentricDualBlock
    {(originalVertexCentroid K v).val, (originalEdgeCentroid K e).val}).space

theorem primalEdgeContact_subset_rim [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ¬ edgeInGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P e)
    (v : K.vertices) :
    primalEdgeContact K e v ⊆
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) := by
  unfold primalEdgeContact
  convert PoincareConjecture.M76.vertexDualRim_contains_selected_unselected_block
    (K := K.barycentricSubdivision)
    (p := originalVertexCentroid K v) (q := originalEdgeCentroid K e)
    (originalVertexCentroid_mem_primalCentroidSet K P hP v)
    (originalEdgeCentroid_not_mem_primalCentroidSet K P hP e he) using 1
  congr 2
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem primalEdgeContact_isFinitePLInterval [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val) :
    ∃ t ∈ K.barycentricSubdivision.faces, ∃ u ∈ K.barycentricSubdivision.faces,
      t.card = 3 ∧ u.card = 3 ∧
      t.centroid ℝ id ≠ u.centroid ℝ id ∧
      IsFinitePLBallPair ℝ (primalEdgeContact K e v)
        {t.centroid ℝ id, u.centroid ℝ id} := by
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, ht⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hpure' : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hc⟩ := hpure s hs
    exact ⟨t, ht, hc, hst⟩
  have hjbound : ∀ s ∈ K.barycentricSubdivision.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, ht, hst⟩ := K.barycentricSubdivision_pure_triangles hpure' s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hadj := originalVertexCentroid_adj_edgeCentroid K e v hv
  have hne : (originalVertexCentroid K v).val ≠ (originalEdgeCentroid K e).val :=
    fun h ↦ hadj.ne (Subtype.ext h)
  have hface : ({(originalVertexCentroid K v).val, (originalEdgeCentroid K e).val} : Finset E) ∈
      K.barycentricSubdivision.faces := by
    have hf := hadj.2
    change (({originalVertexCentroid K v, originalEdgeCentroid K e} :
      Finset K.barycentricSubdivision.vertices).map (Function.Embedding.subtype _)) ∈
      K.barycentricSubdivision.faces at hf
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hf
  obtain ⟨t, ht, u, hu, htc, huc, _, _, hcent, hpair, _⟩ :=
    K.barycentricSubdivision.exists_surface_dual_edge_interval hjbound
      (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces) hne hface
  exact ⟨t, ht, u, hu, htc, huc, hcent, hpair⟩

theorem sameCard_centroid_dualBlocks_disjoint [Fintype K.barycentricSubdivision.faces]
    (s t : K.vertexAbstractComplex.faces) (hne : s ≠ t) (hcard : s.val.card = t.val.card) :
    Disjoint
      (K.barycentricSubdivision.barycentricDualBlock {(K.vertexFaceCentroidGraphIso s).val}).space
      (K.barycentricSubdivision.barycentricDualBlock {(K.vertexFaceCentroidGraphIso t).val}).space := by
  let p := K.vertexFaceCentroidGraphIso s
  let q := K.vertexFaceCentroidGraphIso t
  have hpq : p ≠ q := fun h ↦ hne (K.vertexFaceCentroidGraphIso.injective h)
  have hnot : ({p.val, q.val} : Finset E) ∉ K.barycentricSubdivision.faces := by
    intro hf
    have hadj : K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.Adj p q := by
      refine ⟨hpq, ?_⟩
      change (({p, q} : Finset K.barycentricSubdivision.vertices).map
        (Function.Embedding.subtype _)) ∈ K.barycentricSubdivision.faces
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hf
    exact K.vertexAbstractComplex.toPreAbstractSimplicialComplex.faceInclusionGraph_not_adj_of_card_eq
      s t hcard (K.vertexFaceCentroidGraphIso.map_rel_iff.mp hadj)
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hxy := (K.barycentricSubdivision.vertex_dualBlocks_space_inter p.val q.val).subset ⟨hx, hy⟩
  rw [K.barycentricSubdivision.barycentricDualBlock_space_eq_empty_of_not_face
    (Finset.insert_nonempty _ _) hnot] at hxy
  exact hxy

theorem primalEdgeContact_disjoint [Fintype K.barycentricSubdivision.faces]
    (e f : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v w : K.vertices) (hne : e ≠ f ∨ v ≠ w) :
    Disjoint (primalEdgeContact K e v) (primalEdgeContact K f w) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := (K.barycentricSubdivision.vertex_dualBlocks_space_inter
    (originalVertexCentroid K v).val (originalEdgeCentroid K e).val).symm.subset hx
  have hy' := (K.barycentricSubdivision.vertex_dualBlocks_space_inter
    (originalVertexCentroid K w).val (originalEdgeCentroid K f).val).symm.subset hy
  rcases hne with hef | hvw
  · have hn : (⟨e.val, e.property.1⟩ : K.vertexAbstractComplex.faces) ≠ ⟨f.val, f.property.1⟩ :=
      fun h ↦ hef (Subtype.ext (congrArg (fun z : K.vertexAbstractComplex.faces ↦ z.val) h))
    exact Set.disjoint_left.mp (sameCard_centroid_dualBlocks_disjoint K _ _ hn
      (e.property.2.trans f.property.2.symm)) hx'.2 hy'.2
  · have hn : (⟨{v}, K.vertexAbstractComplex.singleton_mem v⟩ : K.vertexAbstractComplex.faces) ≠
        ⟨{w}, K.vertexAbstractComplex.singleton_mem w⟩ :=
      fun h ↦ hvw (Finset.singleton_injective (congrArg Subtype.val h))
    exact Set.disjoint_left.mp (sameCard_centroid_dualBlocks_disjoint K _ _ hn
      (by simp only [Finset.card_singleton])) hx'.1 hy'.1

noncomputable def primalEdgeMark
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) (v : K.vertices) : E :=
  ({(originalVertexCentroid K v).val, (originalEdgeCentroid K e).val} : Finset E).centroid ℝ id

theorem primalEdgeMark_mem_contact [Fintype K.barycentricSubdivision.faces]
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val) :
    primalEdgeMark K e v ∈ primalEdgeContact K e v := by
  have hadj := originalVertexCentroid_adj_edgeCentroid K e v hv
  have hface : ({(originalVertexCentroid K v).val, (originalEdgeCentroid K e).val} : Finset E) ∈
      K.barycentricSubdivision.faces := by
    have hf := hadj.2
    change (({originalVertexCentroid K v, originalEdgeCentroid K e} :
      Finset K.barycentricSubdivision.vertices).map (Function.Embedding.subtype _)) ∈
      K.barycentricSubdivision.faces at hf
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hf
  exact (K.barycentricSubdivision.barycentricDualBlock _).vertices_subset_space
    (K.barycentricSubdivision.faceCentroid_mem_barycentricDualBlock_vertices hface)

theorem primalEdgeMark_mem_rim [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ¬ edgeInGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P e)
    (v : K.vertices) (hv : v ∈ e.val) :
    primalEdgeMark K e v ∈
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) :=
  primalEdgeContact_subset_rim K P hP e he v (primalEdgeMark_mem_contact K e v hv)

theorem primalEdgeMark_ne [Fintype K.barycentricSubdivision.faces]
    (e f : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v w : K.vertices) (hv : v ∈ e.val) (hw : w ∈ f.val)
    (hne : e ≠ f ∨ v ≠ w) : primalEdgeMark K e v ≠ primalEdgeMark K f w := by
  intro h
  exact Set.disjoint_left.mp (primalEdgeContact_disjoint K e f v w hne)
    (primalEdgeMark_mem_contact K e v hv) (h ▸ primalEdgeMark_mem_contact K f w hw)

theorem four_primalEdgeMarks_injective [Fintype K.barycentricSubdivision.faces]
    (edges : Fin 2 → Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (hedges : Function.Injective edges) (ends : Fin 2 → Fin 2 → K.vertices)
    (hends : ∀ i, Function.Injective (ends i))
    (hmem : ∀ i j, ends i j ∈ (edges i).val) :
    Function.Injective (fun ij : Fin 2 × Fin 2 ↦ primalEdgeMark K (edges ij.1) (ends ij.1 ij.2)) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have hik : i = k := by
    by_contra hne
    exact primalEdgeMark_ne K (edges i) (edges k) (ends i j) (ends k l)
      (hmem i j) (hmem k l) (Or.inl (fun he ↦ hne (hedges he))) h
  subst k
  have hjl : j = l := by
    by_contra hne
    exact primalEdgeMark_ne K (edges i) (edges i) (ends i j) (ends i l)
      (hmem i j) (hmem i l) (Or.inr (fun he ↦ hne (hends i he))) h
  subst l
  rfl

theorem exists_four_primal_rim_marks [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (edges : Fin 2 → Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (hedges : Function.Injective edges)
    (hnonprimal : ∀ i, ¬ edgeInGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P (edges i)) :
    ∃ (ends : Fin 2 → Fin 2 → K.vertices) (marks : Fin 2 × Fin 2 → E),
      (∀ i, (edges i).val = {ends i 0, ends i 1}) ∧
      (∀ i, ends i 0 ≠ ends i 1) ∧
      (∀ ij, marks ij = primalEdgeMark K (edges ij.1) (ends ij.1 ij.2)) ∧
      Function.Injective marks ∧
      ∀ ij, marks ij ∈ K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) := by
  classical
  choose a b hab heq using (fun i : Fin 2 ↦ Finset.card_eq_two.mp (edges i).property.2)
  let ends : Fin 2 → Fin 2 → K.vertices := fun i ↦ ![a i, b i]
  have hends : ∀ i, Function.Injective (ends i) := by
    intro i j k h
    have hne := hab i
    fin_cases j <;> fin_cases k <;> simp_all [ends]
  have hmem : ∀ i j, ends i j ∈ (edges i).val := by
    intro i j
    rw [heq i]
    fin_cases j <;> simp [ends]
  refine ⟨ends, fun ij ↦ primalEdgeMark K (edges ij.1) (ends ij.1 ij.2), ?_, ?_,
    fun _ ↦ rfl, four_primalEdgeMarks_injective K edges hedges ends hends hmem, ?_⟩
  · intro i
    exact heq i
  · intro i
    exact hab i
  · intro ij
    exact primalEdgeMark_mem_rim K P hP (edges ij.1) (hnonprimal ij.1)
      (ends ij.1 ij.2) (hmem ij.1 ij.2)

end PoincareConjecture.M76.OriginalTriangleCopies
