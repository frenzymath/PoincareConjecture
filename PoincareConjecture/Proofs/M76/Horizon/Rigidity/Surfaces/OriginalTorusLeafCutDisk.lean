import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualEdges
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DualTreeDisk
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SurfaceVertexDualDisk
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DualFaceGraph
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalFaceLabels
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.EdgeSubdivisionTree











set_option autoImplicit false
set_option maxHeartbeats 500000

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical

theorem vertexDualRim_eq_iUnion_contacts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (S : Set K.vertices) :
    K.vertexDualRim S =
      ⋃ (p : K.vertices) (_ : p ∈ S) (q : K.vertices) (_ : q ∈ Sᶜ),
        (K.barycentricDualBlock {p.val}).space ∩
          (K.barycentricDualBlock {q.val}).space := by
  ext x
  simp only [Geometry.SimplicialComplex.vertexDualRim,
    Geometry.SimplicialComplex.vertexDualUnion, mem_inter_iff, mem_iUnion,
    exists_prop]
  tauto

noncomputable def dualIncidenceRestriction
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : AbstractSimplicialComplex V)
    (P : SimpleGraph V)
    (D : SimpleGraph (Triangle A.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph A.toPreAbstractSimplicialComplex P) :
    D.incidenceSubdivision ↪g
      (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).incidenceSubdivision where
  toFun := Sum.elim Sum.inl (fun e =>
    Sum.inr ⟨e.val, SimpleGraph.edgeSet_mono hD e.property⟩)
  inj' := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · apply congrArg (fun z : Triangle A.toPreAbstractSimplicialComplex => Sum.inl z)
      exact Sum.inl.inj h
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      cases h
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      cases h
    · change Sum.inr (⟨x.val, _⟩ :
          (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet) =
        Sum.inr ⟨y.val, _⟩ at h
      have h' : (⟨x.val, _⟩ :
          (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet) =
          ⟨y.val, _⟩ := @Sum.inr.inj _ _ _ _ h
      have hxy : x.val = y.val := congrArg
        (fun z : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet =>
          z.val) h'
      exact congrArg (fun z : D.edgeSet => Sum.inr z)
        (Subtype.ext hxy)
  map_rel_iff' := by
    intro x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp only [SimpleGraph.incidenceSubdivision, ne_eq, Sum.inl.injEq,
        Sum.inr.injEq, true_and, false_and, and_false]
    · rfl
    · rfl
    · rfl
    · rfl

theorem exists_original_torus_leaf_cut_disk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hDtree : D.IsTree) :
    ∃ S : Finset K.barycentricSubdivision.vertices,
      (K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
        (S : Set K.barycentricSubdivision.vertices)).IsTree ∧
      IsFinitePLBallPair (ℝ × ℝ)
        (K.barycentricSubdivision.vertexDualUnion (S : Set K.barycentricSubdivision.vertices))
        (K.barycentricSubdivision.vertexDualRim (S : Set K.barycentricSubdivision.vertices)) := by
  classical
  let A := K.vertexAbstractComplex
  let hcounts (e : Edge A.toPreAbstractSimplicialComplex) :
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original e]
    apply hcofaces _ e.property.1
    simpa only [Finset.card_map] using e.property.2
  let q := (dualIncidenceRestriction A P D hD).trans
    (PreAbstractSimplicialComplex.ModTwoCochains.dualFaceGraphEmbedding
      A.toPreAbstractSimplicialComplex P hcounts)
  let p := q.trans K.vertexFaceCentroidGraphIso.toEmbedding
  let S := (Set.toFinite (Set.range p)).toFinset
  have hS : (S : Set K.barycentricSubdivision.vertices) = Set.range p :=
    (Set.toFinite (Set.range p)).coe_toFinset
  have htree :
      (K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
        (S : Set K.barycentricSubdivision.vertices)).IsTree := by
    rw [hS]
    exact (SimpleGraph.Embedding.isoInduceRange p).isTree_iff.mp
      (SimpleGraph.IsTree.incidenceSubdivision _ hDtree)
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, ht⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hpure' : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hcard⟩ := hpure s hs
    exact ⟨t, ht, hcard, hst⟩
  have hball := K.barycentricSubdivision.isFinitePLBallPair_vertexDualUnion_of_induced_tree
    (K.barycentricSubdivision_pure_triangles hpure')
    (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces)
    (fun p hp => K.isConnected_barycentric_vertex_link_of_pure_triangles hpure'
      (fun q hq => by simpa only [K.faceLink_singleton_eq_link] using hlinks q hq) hp)
    S htree
  exact ⟨S, htree, hball⟩




theorem exists_original_torus_leaf_cut_disk_with_dual_embedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hDtree : D.IsTree) :
    ∃ (r : (complementaryTriangleGraph
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision ↪g
        K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
      (p : D.incidenceSubdivision ↪g
        K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
      (S : Finset K.barycentricSubdivision.vertices),
      p = (dualIncidenceRestriction K.vertexAbstractComplex P D hD).trans r ∧
      (S : Set K.barycentricSubdivision.vertices) = Set.range p ∧
      (K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
        (S : Set K.barycentricSubdivision.vertices)).IsTree ∧
      IsFinitePLBallPair (ℝ × ℝ)
        (K.barycentricSubdivision.vertexDualUnion (S : Set K.barycentricSubdivision.vertices))
        (K.barycentricSubdivision.vertexDualRim (S : Set K.barycentricSubdivision.vertices)) := by
  classical
  let A := K.vertexAbstractComplex
  let hcounts (e : Edge A.toPreAbstractSimplicialComplex) :
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original e]
    apply hcofaces _ e.property.1
    simpa only [Finset.card_map] using e.property.2
  let r := (PreAbstractSimplicialComplex.ModTwoCochains.dualFaceGraphEmbedding
      A.toPreAbstractSimplicialComplex P hcounts).trans
    K.vertexFaceCentroidGraphIso.toEmbedding
  let p := (dualIncidenceRestriction A P D hD).trans r
  let S := (Set.toFinite (Set.range p)).toFinset
  have hS : (S : Set K.barycentricSubdivision.vertices) = Set.range p :=
    (Set.toFinite (Set.range p)).coe_toFinset
  have htree :
      (K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
        (S : Set K.barycentricSubdivision.vertices)).IsTree := by
    rw [hS]
    exact (SimpleGraph.Embedding.isoInduceRange p).isTree_iff.mp
      (SimpleGraph.IsTree.incidenceSubdivision _ hDtree)
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, ht⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hpure' : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hcard⟩ := hpure s hs
    exact ⟨t, ht, hcard, hst⟩
  have hball := K.barycentricSubdivision.isFinitePLBallPair_vertexDualUnion_of_induced_tree
    (K.barycentricSubdivision_pure_triangles hpure')
    (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces)
    (fun p hp => K.isConnected_barycentric_vertex_link_of_pure_triangles hpure'
      (fun q hq => by simpa only [K.faceLink_singleton_eq_link] using hlinks q hq) hp)
    S htree
  exact ⟨r, p, S, rfl, hS, htree, hball⟩

theorem selected_triangle_mem_of_leaf_cut_embedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    {D : SimpleGraph (Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (p : D.incidenceSubdivision ↪g
        K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
    {S : Set K.barycentricSubdivision.vertices}
    (hS : S = Set.range p)
    (q : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    p (Sum.inl q) ∈ S := by
  rw [hS]
  exact ⟨Sum.inl q, rfl⟩

theorem vertexDualRim_contains_selected_unselected_block
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : SimplicialComplex ℝ E} [Fintype K.faces]
    {S : Set K.vertices} {p q : K.vertices}
    (hp : p ∈ S) (hq : q ∈ Sᶜ) :
    (K.barycentricDualBlock {p.val, q.val}).space ⊆
      K.vertexDualRim S := by
  rw [vertexDualRim_eq_iUnion_contacts K S]
  intro x hx
  exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, mem_iUnion.mpr ⟨q,
    mem_iUnion.mpr ⟨hq, by
      rw [K.barycentricDualBlock_space_inter]
      exact hx⟩⟩⟩⟩

theorem exists_original_torus_leaf_cut_disk_of_euler_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (c : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hzero : (K.edgeComponentComplex c).surfaceEulerCount = 0) :
    let J := K.edgeComponentComplex c
    let : Fintype J.vertices :=
      (J.finite_vertices_of_finite_faces
        (hK.subset (K.edgeComponentComplex_le c))).fintype
    let : Fintype J.faces :=
      (hK.subset (K.edgeComponentComplex_le c)).fintype
    let : Fintype J.barycentricSubdivision.faces := J.barycentricSubdivision_finite.fintype
    ∃ (P : SimpleGraph J.vertices),
      P ≤ J.vertexAbstractComplex.edgeGraph ∧ P.IsTree ∧
      ∃ (D : SimpleGraph (Triangle
          J.vertexAbstractComplex.toPreAbstractSimplicialComplex)),
        D ≤ complementaryTriangleGraph
          J.vertexAbstractComplex.toPreAbstractSimplicialComplex P ∧
        D.IsTree ∧
        ∃ (L : Finset (Edge
            J.vertexAbstractComplex.toPreAbstractSimplicialComplex))
          (S : Finset J.barycentricSubdivision.vertices),
          L.card = 2 ∧
          (J.barycentricSubdivision.vertexAbstractComplex.edgeGraph.induce
            (S : Set J.barycentricSubdivision.vertices)).IsTree ∧
          IsFinitePLBallPair (ℝ × ℝ)
            (J.barycentricSubdivision.vertexDualUnion
              (S : Set J.barycentricSubdivision.vertices))
            (J.barycentricSubdivision.vertexDualRim
              (S : Set J.barycentricSubdivision.vertices)) := by
  classical
  let J := K.edgeComponentComplex c
  letI : Fintype J.vertices :=
    (J.finite_vertices_of_finite_faces
      (hK.subset (K.edgeComponentComplex_le c))).fintype
  letI : Fintype J.faces :=
    (hK.subset (K.edgeComponentComplex_le c)).fintype
  letI : Fintype J.barycentricSubdivision.faces := J.barycentricSubdivision_finite.fintype
  obtain ⟨P, hP, hPtree, D, hD, hDtree, L, hL, hLnot, hLcard⟩ :=
    exists_original_torus_residual_edges K hK hpure hcofaces hlinks c hzero
  have hpureJ : ∀ s ∈ J.faces, ∃ t ∈ J.faces, s ⊆ t ∧ t.card = 3 := by
    intro s hs
    obtain ⟨t, ht, hst, hcard⟩ := K.edgeComponentComplex_pure c hpure s hs
    exact ⟨t, ht, hst, hcard⟩
  have hcofacesJ : ∀ s ∈ J.faces, s.card = 2 →
      {t : Finset E | t ∈ J.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
    intro s hs hscard
    rw [K.edgeComponentComplex_cofaces c hs 3]
    exact hcofaces s (K.edgeComponentComplex_le c hs) hscard
  have hlinksJ : ∀ p ∈ J.vertices, IsConnected (J.faceLink {p}).space := by
    intro p hp
    rw [K.edgeComponentComplex_vertex_link c hp]
    exact hlinks p (K.edgeComponentComplex_le c hp)
  obtain ⟨S, hStree, hSball⟩ := exists_original_torus_leaf_cut_disk J
    hpureJ hcofacesJ hlinksJ P D hD hDtree
  exact ⟨P, hP, hPtree, D, hD, hDtree, L, S, hLcard, hStree, hSball⟩

end PoincareConjecture.M76
