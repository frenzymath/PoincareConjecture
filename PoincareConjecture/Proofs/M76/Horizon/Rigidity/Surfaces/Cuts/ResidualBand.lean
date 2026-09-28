import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ResidualBridges









set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  [Fintype K.barycentricSubdivision.faces]

noncomputable def residualBand
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) : Set E :=
  (K.barycentricSubdivision.barycentricDualBlock {(originalEdgeCentroid K e).val}).space

noncomputable def residualBandRim
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) : Set E :=
  (K.barycentricSubdivision.barycentricSubdivision.link (originalEdgeCentroid K e).val).space

noncomputable def residualCofaceContact
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) (t : Finset E) : Set E :=
  (K.barycentricSubdivision.barycentricDualBlock
    {(originalEdgeCentroid K e).val, t.centroid ℝ id}).space

theorem residualBand_isFinitePLDisk
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    IsFinitePLBallPair (ℝ × ℝ) (residualBand K e) (residualBandRim K e) := by
  have hpure' : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hc⟩ := hpure s hs
    exact ⟨t, ht, hc, hst⟩
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, hc⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq hc
  exact K.barycentricSubdivision.isFinitePLBallPair_barycentricDualBlock_vertex
    (K.barycentricSubdivision_pure_triangles hpure')
    (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces)
    (originalEdgeCentroid K e).property
    (K.isConnected_barycentric_vertex_link_of_pure_triangles hpure'
      (fun p hp ↦ by simpa only [K.faceLink_singleton_eq_link] using hlinks p hp)
      (originalEdgeCentroid K e).property)

omit [FiniteDimensional ℝ E] [Fintype K.barycentricSubdivision.faces] in
private theorem edgeBand_neighbor_cases
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b})
    {t u : Finset E}
    (hcofaces : {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
      ({a.val, b.val} : Finset E) ⊆ s} = {t, u})
    (q : E) (hq : q ≠ (originalEdgeCentroid K e).val)
    (hface : ({(originalEdgeCentroid K e).val, q} : Finset E) ∈
      K.barycentricSubdivision.faces) :
    q = a.val ∨ q = b.val ∨ q = t.centroid ℝ id ∨ q = u.centroid ℝ id := by
  have hqv := K.barycentricSubdivision.face_subset_vertices hface
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
  obtain ⟨s, hs, hsq⟩ := (K.mem_barycentricSubdivision_vertices_iff q).mp hqv
  have heface : ({a.val, b.val} : Finset E) ∈ K.faces := by
    have hh := e.property.1
    change e.val.map (Function.Embedding.subtype _) ∈ K.faces at hh
    simpa only [heq, Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] using hh
  have hcent : (originalEdgeCentroid K e).val =
      ({a.val, b.val} : Finset E).centroid ℝ id := by
    change (e.val.map (Function.Embedding.subtype _)).centroid ℝ id = _
    simp only [heq, Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype]
  have hcard : ({a.val, b.val} : Finset E).card = 2 := by
    have hh := e.property.2
    simpa only [heq, Finset.card_map, Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] using
      (show (e.val.map (Function.Embedding.subtype _)).card = 2 by simpa using hh)
  have hne : s ≠ {a.val, b.val} := by
    intro h
    exact hq (by rw [← hsq, h, ← hcent])
  rw [hcent, ← hsq] at hface
  rcases (K.barycentric_centroid_pair_face_iff ⟨_, heface⟩ ⟨s, hs⟩).mp hface with
    hsub | hsub
  · change ({a.val, b.val} : Finset E) ⊆ s at hsub
    have hcard' : s.card = 3 := by
      have hle := Finset.card_le_card hsub
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩)
      have hb := hbound s hs
      omega
    have hh := hcofaces.subset ⟨hs, hcard', hsub⟩
    rcases hh with rfl | hh
    · exact Or.inr (Or.inr (Or.inl hsq.symm))
    · have hh' : s = u := hh
      exact Or.inr (Or.inr (Or.inr (by rw [← hh']; exact hsq.symm)))
  · change s ⊆ ({a.val, b.val} : Finset E) at hsub
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hpos := (K.nonempty_of_mem_faces hs).card_pos
    have hc : s.card = 1 := by omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    have hv := hsub (Finset.mem_singleton_self v)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    have hqv' : q = v := by simpa only [Finset.centroid_singleton, id_eq] using hsq.symm
    rcases hv with hv | hv
    · exact Or.inl (hqv'.trans hv)
    · exact Or.inr (Or.inl (hqv'.trans hv))

theorem primalEdgeContact_subset_bandRim
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val) :
    primalEdgeContact K e v ⊆ residualBandRim K e := by
  have hadj := originalVertexCentroid_adj_edgeCentroid K e v hv
  exact fun _ hx ↦ (K.barycentricSubdivision.dualEdge_space_subset_vertex_links
    (originalVertexCentroid K v).property (originalEdgeCentroid K e).property
    (fun h ↦ hadj.ne (Subtype.ext h)) hx).2

omit [FiniteDimensional ℝ E] [Fintype K.barycentricSubdivision.faces] in
theorem originalEdgeCentroid_ne_triangleCentroid
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3) :
    (originalEdgeCentroid K e).val ≠ t.centroid ℝ id := by
  intro h
  have hh : (⟨e.val.map (Function.Embedding.subtype _), e.property.1⟩ : K.faces) = ⟨t, ht⟩ :=
    K.faceCentroid_injective h
  have hc := congrArg (fun s : K.faces ↦ s.val.card) hh
  change (e.val.map (Function.Embedding.subtype _)).card = t.card at hc
  rw [Finset.card_map, e.property.2, htc] at hc
  omega

theorem residualCofaceContact_subset_bandRim
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3) :
    residualCofaceContact K e t ⊆ residualBandRim K e := by
  have htv : t.centroid ℝ id ∈ K.barycentricSubdivision.vertices :=
    (K.mem_barycentricSubdivision_vertices_iff _).mpr ⟨t, ht, rfl⟩
  exact fun _ hx ↦ (K.barycentricSubdivision.dualEdge_space_subset_vertex_links
    (originalEdgeCentroid K e).property htv
    (originalEdgeCentroid_ne_triangleCentroid K e ht htc) hx).1


theorem residualBandRim_eq_four_contacts
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b})
    {t u : Finset E}
    (hcofaces : {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
      ({a.val, b.val} : Finset E) ⊆ s} = {t, u}) :
    residualBandRim K e = primalEdgeContact K e a ∪ primalEdgeContact K e b ∪
      residualCofaceContact K e t ∪ residualCofaceContact K e u := by
  have ht : t ∈ K.faces ∧ t.card = 3 ∧ ({a.val, b.val} : Finset E) ⊆ t :=
    hcofaces.symm.subset (Or.inl rfl)
  have hu : u ∈ K.faces ∧ u.card = 3 ∧ ({a.val, b.val} : Finset E) ⊆ u :=
    hcofaces.symm.subset (Or.inr rfl)
  apply Subset.antisymm
  · intro x hx
    rw [residualBandRim,
      K.barycentricSubdivision.barycentric_vertex_link_space_eq_iUnion_dualEdges
        (originalEdgeCentroid K e).property] at hx
    obtain ⟨q, hq, hx⟩ := mem_iUnion₂.mp hx
    rcases edgeBand_neighbor_cases K hbound e heq hcofaces q hq.1 hq.2 with
      rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (by
        simpa only [primalEdgeContact, originalVertexCentroid_val, Finset.pair_comm] using hx)))
    · exact Or.inl (Or.inl (Or.inr (by
        simpa only [primalEdgeContact, originalVertexCentroid_val, Finset.pair_comm] using hx)))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  · exact union_subset
      (union_subset (union_subset
        (primalEdgeContact_subset_bandRim K e a (by simp [heq]))
        (primalEdgeContact_subset_bandRim K e b (by simp [heq])))
        (residualCofaceContact_subset_bandRim K e ht.1 ht.2.1))
      (residualCofaceContact_subset_bandRim K e hu.1 hu.2.1)

omit [FiniteDimensional ℝ E] [Fintype K.barycentricSubdivision.faces] in
private theorem centroid_flag_triangle_face
    {v : E} {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hv : v ∈ s) (hst : s ⊆ t) :
    ({v, s.centroid ℝ id, t.centroid ℝ id} : Finset E) ∈
      K.barycentricSubdivision.faces := by
  apply (K.barycentricSubdivision_faces_of_face_chains _).mpr
  refine ⟨{{v}, s, t}, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty _)
    · exact hs
    · exact ht
  · intro u hu w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
    have hvs : ({v} : Finset E) ⊆ s := Finset.singleton_subset_iff.mpr hv
    have hvt := hvs.trans hst
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    all_goals first | exact Or.inl Subset.rfl | exact Or.inl hvs | exact Or.inr hvs |
      exact Or.inl hvt | exact Or.inr hvt | exact Or.inl hst | exact Or.inr hst
  · simp only [Finset.image_insert, Finset.image_singleton, Finset.centroid_singleton, id_eq]

noncomputable def residualBandCorner
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (t : Finset E) : E :=
  ({v.val, (originalEdgeCentroid K e).val, t.centroid ℝ id} : Finset E).centroid ℝ id

private theorem edge_flag_triangle_face
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {v : K.vertices} (hv : v ∈ e.val) {t : Finset E} (ht : t ∈ K.faces)
    (het : e.val.map (Function.Embedding.subtype _) ⊆ t) :
    ({v.val, (originalEdgeCentroid K e).val, t.centroid ℝ id} : Finset E) ∈
      K.barycentricSubdivision.faces := by
  exact centroid_flag_triangle_face K e.property.1 ht
    (Finset.mem_map.mpr ⟨v, hv, rfl⟩) het

omit [FiniteDimensional ℝ E] [DecidableEq E] [Fintype K.barycentricSubdivision.faces] in
private theorem vertex_ne_triangleCentroid (v : K.vertices)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3) :
    v.val ≠ t.centroid ℝ id := by
  intro h
  have h' : ({v.val} : Finset E).centroid ℝ id = t.centroid ℝ id := by
    simpa only [Finset.centroid_singleton, id_eq] using h
  have hh : (⟨{v.val}, v.property⟩ : K.faces) = ⟨t, ht⟩ := K.faceCentroid_injective h'
  have hc := congrArg (fun s : K.faces ↦ s.val.card) hh
  change ({v.val} : Finset E).card = t.card at hc
  rw [Finset.card_singleton, htc] at hc
  omega

omit [Fintype K.barycentricSubdivision.faces] in
private theorem contact_interval_of_flag_triangles
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    {p q r w : E} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpw : p ≠ w) (hqw : q ≠ w) (hrw : r ≠ w)
    (hr : ({p, q, r} : Finset E) ∈ K.faces)
    (hw : ({p, q, w} : Finset E) ∈ K.faces) :
    IsFinitePLBallPair ℝ (K.barycentricDualBlock {p, q}).space
      {({p, q, r} : Finset E).centroid ℝ id, ({p, q, w} : Finset E).centroid ℝ id} := by
  have he : ({p, q} : Finset E) ∈ K.faces :=
    K.down_closed hr (by simp) (Finset.insert_nonempty _ _)
  have hrc : ({p, q, r} : Finset E).card = 3 := by simp [hpq, hpr, hqr]
  have hwc : ({p, q, w} : Finset E).card = 3 := by simp [hpq, hpw, hqw]
  have hne : ({p, q, r} : Finset E) ≠ {p, q, w} := by
    intro h
    have hh : r ∈ ({p, q, w} : Finset E) := h ▸ (by simp)
    simp [Ne.symm hpr, Ne.symm hqr, hrw] at hh
  have hsub : ({({p, q, r} : Finset E), {p, q, w}} : Set (Finset E)) ⊆
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ ({p, q} : Finset E) ⊆ t} := by
    rintro t (rfl | ht)
    · exact ⟨hr, hrc, by simp⟩
    · have ht' : t = {p, q, w} := ht
      subst t
      exact ⟨hw, hwc, by simp⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_pair hne, hcofaces _ he (Finset.card_pair hpq)]) (Set.toFinite _)
  exact (K.isFinitePLBallPair_barycentricDualBlock_of_paired_facet hbound he hr hw
    (Finset.card_pair hpq) hrc hwc (by simp) (by simp) hne
    (fun t ht hst hc ↦ heq.symm.subset ⟨ht, hc, hst⟩)).1

theorem primalEdgeContact_exact_interval
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val)
    {t u : Finset E} (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (htc : t.card = 3) (huc : u.card = 3) (htu : t ≠ u)
    (het : e.val.map (Function.Embedding.subtype _) ⊆ t)
    (heu : e.val.map (Function.Embedding.subtype _) ⊆ u) :
    IsFinitePLBallPair ℝ (primalEdgeContact K e v)
      {residualBandCorner K e v t, residualBandCorner K e v u} := by
  have hve : v.val ≠ (originalEdgeCentroid K e).val := by
    rw [← originalVertexCentroid_val K v]
    exact fun h ↦ (originalVertexCentroid_adj_edgeCentroid K e v hv).ne (Subtype.ext h)
  have htu' : t.centroid ℝ id ≠ u.centroid ℝ id := by
    intro h
    exact htu (congrArg Subtype.val
      (K.faceCentroid_injective h : (⟨t, ht⟩ : K.faces) = ⟨u, hu⟩))
  have h := contact_interval_of_flag_triangles K.barycentricSubdivision
    (K.barycentricSubdivision_card_le (N := 2) hbound)
    (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces)
    hve (vertex_ne_triangleCentroid K v ht htc)
    (originalEdgeCentroid_ne_triangleCentroid K e ht htc)
    (vertex_ne_triangleCentroid K v hu huc)
    (originalEdgeCentroid_ne_triangleCentroid K e hu huc) htu'
    (edge_flag_triangle_face K e hv ht het) (edge_flag_triangle_face K e hv hu heu)
  simpa only [primalEdgeContact, originalVertexCentroid_val, residualBandCorner] using h

theorem residualCofaceContact_exact_interval
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (hab : a ≠ b) (heq : e.val = {a, b})
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3)
    (het : e.val.map (Function.Embedding.subtype _) ⊆ t) :
    IsFinitePLBallPair ℝ (residualCofaceContact K e t)
      {residualBandCorner K e a t, residualBandCorner K e b t} := by
  have hve (v : K.vertices) (hv : v ∈ e.val) :
      v.val ≠ (originalEdgeCentroid K e).val := by
    rw [← originalVertexCentroid_val K v]
    exact fun h ↦ (originalVertexCentroid_adj_edgeCentroid K e v hv).ne (Subtype.ext h)
  have hperm (v : E) :
      ({(originalEdgeCentroid K e).val, t.centroid ℝ id, v} : Finset E) =
        {v, (originalEdgeCentroid K e).val, t.centroid ℝ id} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h := contact_interval_of_flag_triangles K.barycentricSubdivision
    (K.barycentricSubdivision_card_le (N := 2) hbound)
    (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces)
    (originalEdgeCentroid_ne_triangleCentroid K e ht htc)
    (Ne.symm (hve a (by simp [heq]))) (Ne.symm (vertex_ne_triangleCentroid K a ht htc))
    (Ne.symm (hve b (by simp [heq]))) (Ne.symm (vertex_ne_triangleCentroid K b ht htc))
    (fun h ↦ hab (Subtype.ext h))
    (hperm a.val ▸ edge_flag_triangle_face K e (by simp [heq]) ht het)
    (hperm b.val ▸ edge_flag_triangle_face K e (by simp [heq]) ht het)
  simpa only [hperm, residualCofaceContact, residualBandCorner] using h

theorem primal_coface_contact_inter
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3)
    (het : e.val.map (Function.Embedding.subtype _) ⊆ t) :
    primalEdgeContact K e v ∩ residualCofaceContact K e t = {residualBandCorner K e v t} := by
  have hve : v.val ≠ (originalEdgeCentroid K e).val := by
    rw [← originalVertexCentroid_val K v]
    exact fun h ↦ (originalVertexCentroid_adj_edgeCentroid K e v hv).ne (Subtype.ext h)
  have hvt := vertex_ne_triangleCentroid K v ht htc
  have het' := originalEdgeCentroid_ne_triangleCentroid K e ht htc
  have hcard : ({v.val, (originalEdgeCentroid K e).val, t.centroid ℝ id} : Finset E).card = 3 := by
    simp [hve, hvt, het']
  have hface := edge_flag_triangle_face K e hv ht het
  rw [primalEdgeContact, originalVertexCentroid_val, residualCofaceContact,
    K.barycentricSubdivision.barycentricDualBlock_space_inter]
  have hunion : ({v.val, (originalEdgeCentroid K e).val} ∪
      {(originalEdgeCentroid K e).val, t.centroid ℝ id} : Finset E) =
      {v.val, (originalEdgeCentroid K e).val, t.centroid ℝ id} := by ext x; simp
  rw [hunion]
  apply K.barycentricSubdivision.barycentricDualBlock_space_eq_centroid_of_maximal hface
  intro s hs hsub
  exact (Finset.eq_of_subset_of_card_le hsub
    ((K.barycentricSubdivision_card_le (N := 2) hbound s hs).trans_eq hcard.symm)).symm

theorem residualCofaceContact_disjoint
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {t u : Finset E} (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (htc : t.card = 3) (huc : u.card = 3) (htu : t ≠ u) :
    Disjoint (residualCofaceContact K e t) (residualCofaceContact K e u) := by
  have hnot : ({t.centroid ℝ id, u.centroid ℝ id} : Finset E) ∉
      K.barycentricSubdivision.faces := by
    intro hh
    rcases (K.barycentric_centroid_pair_face_iff ⟨t, ht⟩ ⟨u, hu⟩).mp hh with hs | hs
    · exact htu (Finset.eq_of_subset_of_card_le hs (by simp only [htc, huc, le_refl]))
    · exact htu (Finset.eq_of_subset_of_card_le hs (by simp only [htc, huc, le_refl])).symm
  apply Set.disjoint_iff_inter_eq_empty.mpr
  rw [residualCofaceContact, residualCofaceContact,
    K.barycentricSubdivision.barycentricDualBlock_space_inter]
  apply K.barycentricSubdivision.barycentricDualBlock_space_eq_empty_of_not_face
    (Finset.union_nonempty.mpr (Or.inl (Finset.insert_nonempty _ _)))
  intro hf
  apply hnot
  exact K.barycentricSubdivision.down_closed hf (by simp) (Finset.insert_nonempty _ _)



theorem exists_residualBand_rim_inventory
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    ∃ a b : K.vertices, ∃ t u : Finset E,
      a ≠ b ∧ e.val = {a, b} ∧ t ≠ u ∧
      (t ∈ K.faces ∧ t.card = 3 ∧ e.val.map (Function.Embedding.subtype _) ⊆ t) ∧
      (u ∈ K.faces ∧ u.card = 3 ∧ e.val.map (Function.Embedding.subtype _) ⊆ u) ∧
      residualBandRim K e = primalEdgeContact K e a ∪ primalEdgeContact K e b ∪
        residualCofaceContact K e t ∪ residualCofaceContact K e u := by
  obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp e.property.2
  have hm : e.val.map (Function.Embedding.subtype _) = {a.val, b.val} := by
    simp only [heq, Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
  have hc : (e.val.map (Function.Embedding.subtype _)).card = 2 := by
    rw [Finset.card_map, e.property.2]
  obtain ⟨t, u, htu, hset⟩ := Set.ncard_eq_two.mp (hcofaces _ e.property.1 hc)
  have ht : t ∈ K.faces ∧ t.card = 3 ∧ e.val.map (Function.Embedding.subtype _) ⊆ t :=
    hset.symm.subset (Or.inl rfl)
  have hu : u ∈ K.faces ∧ u.card = 3 ∧ e.val.map (Function.Embedding.subtype _) ⊆ u :=
    hset.symm.subset (Or.inr rfl)
  refine ⟨a, b, t, u, hab, heq, htu, ht, hu, ?_⟩
  apply residualBandRim_eq_four_contacts K hbound e heq
  rwa [hm] at hset

theorem primalEdgeMark_ne_bandCorner
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3)
    (het : e.val.map (Function.Embedding.subtype _) ⊆ t) :
    primalEdgeMark K e v ≠ residualBandCorner K e v t := by
  have hve : v.val ≠ (originalEdgeCentroid K e).val := by
    rw [← originalVertexCentroid_val K v]
    exact fun h ↦ (originalVertexCentroid_adj_edgeCentroid K e v hv).ne (Subtype.ext h)
  have hvt := vertex_ne_triangleCentroid K v ht htc
  have het' := originalEdgeCentroid_ne_triangleCentroid K e ht htc
  have hface := edge_flag_triangle_face K e hv ht het
  have hpair : ({v.val, (originalEdgeCentroid K e).val} : Finset E) ∈
      K.barycentricSubdivision.faces :=
    K.barycentricSubdivision.down_closed hface (by simp) (Finset.insert_nonempty _ _)
  intro h
  simp only [primalEdgeMark, originalVertexCentroid_val, residualBandCorner] at h
  have hh : (⟨_, hpair⟩ : K.barycentricSubdivision.faces) = ⟨_, hface⟩ :=
    K.barycentricSubdivision.faceCentroid_injective h
  have hc := congrArg (fun s : K.barycentricSubdivision.faces ↦ s.val.card) hh
  change ({v.val, (originalEdgeCentroid K e).val} : Finset E).card =
    ({v.val, (originalEdgeCentroid K e).val, t.centroid ℝ id} : Finset E).card at hc
  simp [hve, hvt, het'] at hc

theorem primalEdgeMark_not_mem_cofaceContact
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3)
    (het : e.val.map (Function.Embedding.subtype _) ⊆ t) :
    primalEdgeMark K e v ∉ residualCofaceContact K e t := by
  intro hx
  exact primalEdgeMark_ne_bandCorner K e v hv ht htc het
    ((primal_coface_contact_inter K hbound e v hv ht htc het).subset
      ⟨primalEdgeMark_mem_contact K e v hv, hx⟩)

end PoincareConjecture.M76.OriginalTriangleCopies
