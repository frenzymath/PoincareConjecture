import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.DerivedComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.MarkedTriangleComponents
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleCofaceConstancy
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseLinkSection










set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

omit [FiniteDimensional ℝ E] in
private theorem centroid_flag_face {v : E} {e t : Finset E}
    (he : e ∈ K.faces) (ht : t ∈ K.faces) (hve : v ∈ e) (het : e ⊆ t) :
    {v, e.centroid ℝ id, t.centroid ℝ id} ∈ K.barycentricSubdivision.faces := by
  classical
  have hv : {v} ∈ K.faces := K.down_closed he (by simpa) (by simp)
  apply (K.barycentricSubdivision_faces_of_face_chains _).mpr
  refine ⟨{{v}, e, t}, Finset.insert_nonempty _ _, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hv
    · exact he
    · exact ht
  · intro s hs u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs hu
    rcases hs with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl
    · exact Or.inl subset_rfl
    · exact Or.inl (Finset.singleton_subset_iff.mpr hve)
    · exact Or.inl (Finset.singleton_subset_iff.mpr (het hve))
    · exact Or.inr (Finset.singleton_subset_iff.mpr hve)
    · exact Or.inl subset_rfl
    · exact Or.inl het
    · exact Or.inr (Finset.singleton_subset_iff.mpr (het hve))
    · exact Or.inr het
    · exact Or.inl subset_rfl
  · simp only [Finset.image_insert, Finset.image_singleton, Finset.centroid_singleton, id_eq]

omit [FiniteDimensional ℝ E] [DecidableEq E] in
private theorem vertex_ne_centroid {t : Finset E} (ht : t ∈ K.faces) (htc : 2 ≤ t.card)
    {v : E} (hv : v ∈ t) : v ≠ t.centroid ℝ id := by
  intro h
  have hvK : {v} ∈ K.faces := K.down_closed ht
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty _)
  have heq := congrArg Subtype.val (K.faceCentroid_injective
    (a₁ := ⟨{v}, hvK⟩) (a₂ := ⟨t, ht⟩)
    ((Finset.centroid_singleton ℝ id v).trans h))
  have hc := congrArg Finset.card heq
  simp only [Finset.card_singleton] at hc
  omega

omit [FiniteDimensional ℝ E] in

theorem closedFaceComplement_link_at_original_vertex
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    {v : E} (hv : v ∈ K.vertices) (hvL : v ∉ L.vertices) :
    (K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).link v =
      K.barycentricSubdivision.link v := by
  ext s
  constructor
  · exact fun hs ↦ ⟨hs.1.1, hs.2.1, hs.2.2.1⟩
  · intro hs
    have hstar : insert v s ∈ (K.barycentricSubdivision.closedStar v).faces := by
      exact ⟨hs.2.2, by simpa only [Finset.insert_idem] using hs.2.2⟩
    have hkeep := K.unmarked_vertex_star_le_closedFaceComplement L hpure hv hvL hstar
    exact ⟨(K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).down_closed
      hkeep (Finset.subset_insert _ _) (K.barycentricSubdivision.nonempty_of_mem_faces hs.1),
      hs.2.1, hkeep⟩

omit [FiniteDimensional ℝ E] in


private theorem link_reaches_unmarked_vertex
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    {t : Finset E} (ht : t ∈ K.faces) (htc : 2 ≤ t.card)
    (x : ((K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).link (t.centroid ℝ id)).vertices) :
    let J := (K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).link (t.centroid ℝ id)
    ∃ v, v ∈ t ∧ v ∉ L.vertices ∧ ∃ hvJ : v ∈ J.vertices,
      J.vertexAbstractComplex.edgeGraph.Reachable x ⟨v, hvJ⟩ := by
  classical
  let C := K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)
  let w := t.centroid ℝ id
  let J := C.link w
  obtain ⟨v, hvK, hvL, hstar⟩ := (K.closedFaceComplement_derived_face_iff L hpure).mp
    x.property.2.2
  have hstar' := hstar
  rw [← K.barycentricDualBlock_singleton_eq_closedStar hvK] at hstar'
  obtain ⟨u, hu, hvu, huw⟩ := hstar'.2 w (Finset.mem_insert_self _ _)
  have hut : u = t := congrArg Subtype.val
    (K.faceCentroid_injective (a₁ := ⟨u, hu⟩) (a₂ := ⟨t, ht⟩) huw)
  have hvt : v ∈ t := hut ▸ hvu (Finset.mem_singleton_self _)
  have hvw : v ≠ w := K.vertex_ne_centroid ht htc hvt
  have htr : insert v (insert w ({(x : E)} : Finset E)) ∈ C.faces := by
    apply K.unmarked_vertex_star_le_closedFaceComplement L hpure hvK hvL
    exact ⟨hstar.2, by simpa only [Finset.insert_idem] using hstar.2⟩
  have hedge : ({v, (x : E)} : Finset E) ∈ J.faces := by
    refine ⟨C.down_closed htr (by intro y hy; simp only [Finset.mem_insert,
      Finset.mem_singleton] at hy ⊢; tauto) (Finset.insert_nonempty _ _), ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hvw.symm, fun h ↦ x.property.2.1 (Finset.mem_singleton.mpr h)⟩
    · simpa only [Finset.insert_comm] using htr
  have hvJ : v ∈ J.vertices := J.down_closed hedge (by simp) (by simp)
  exact ⟨v, hvt, hvL, hvJ, J.reachable_vertices_of_mem_face hedge x ⟨v, hvJ⟩
    (by simp) (by simp)⟩

omit [FiniteDimensional ℝ E] in
private theorem unmarked_vertices_reachable
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    {t : Finset E} (ht : t ∈ K.faces) (htc : 2 ≤ t.card)
    {v u : E} (hv : v ∈ t) (hu : u ∈ t) (hvL : v ∉ L.vertices) (huL : u ∉ L.vertices)
    (hvJ : v ∈ ((K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).link (t.centroid ℝ id)).vertices)
    (huJ : u ∈ ((K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).link (t.centroid ℝ id)).vertices) :
    ((K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).link
      (t.centroid ℝ id)).vertexAbstractComplex.edgeGraph.Reachable ⟨v, hvJ⟩ ⟨u, huJ⟩ := by
  classical
  by_cases hvu : v = u
  · subst u
    exact SimpleGraph.Reachable.refl _
  let C := K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)
  let w := t.centroid ℝ id
  let J := C.link w
  obtain ⟨e, he, het, hve, hue, hetne⟩ : ∃ e ∈ K.faces,
      (e ⊆ t ∨ t ⊆ e) ∧ v ∈ e ∧ u ∈ e ∧ e ≠ t := by
    obtain ⟨q, hq, hqc, htq⟩ := hpure t ht
    have htc' : t.card ≤ 3 := (Finset.card_le_card htq).trans_eq hqc
    by_cases ht2 : t.card = 2
    · exact ⟨q, hq, Or.inr htq, htq hv, htq hu,
        fun h ↦ by have := congrArg Finset.card h; omega⟩
    · have ht3 : t.card = 3 := by omega
      have hpair : ({v, u} : Finset E) ⊆ t := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hv
        · exact Finset.mem_singleton.mp ha ▸ hu
      exact ⟨{v, u}, K.down_closed ht hpair (by simp),
        Or.inl hpair, by simp, by simp,
        fun h ↦ by have := congrArg Finset.card h; simp [Finset.card_pair hvu, ht3] at this⟩
  let c := e.centroid ℝ id
  have hcw : c ≠ w := fun h ↦ hetne (congrArg Subtype.val
    (K.faceCentroid_injective (a₁ := ⟨e, he⟩) (a₂ := ⟨t, ht⟩) h))
  have hedge (a : E) (hat : a ∈ t) (hae : a ∈ e) (haL : a ∉ L.vertices) :
      ({a, c} : Finset E) ∈ J.faces := by
    have haK : a ∈ K.vertices := K.down_closed ht
      (Finset.singleton_subset_iff.mpr hat) (Finset.singleton_nonempty _)
    have hfine : ({a, w, c} : Finset E) ∈ K.barycentricSubdivision.faces := by
      rcases het with het | hte
      · change {a, t.centroid ℝ id, e.centroid ℝ id} ∈ K.barycentricSubdivision.faces
        simpa only [Finset.pair_comm (t.centroid ℝ id) (e.centroid ℝ id)] using
          K.centroid_flag_face he ht hae het
      · exact K.centroid_flag_face ht he hat hte
    have hface : ({a, w, c} : Finset E) ∈ C.faces :=
      K.unmarked_vertex_star_le_closedFaceComplement L hpure haK haL
        ⟨hfine, by simpa only [Finset.insert_idem] using hfine⟩
    refine ⟨C.down_closed hface (by intro z hz; simp only [Finset.mem_insert,
      Finset.mem_singleton] at hz ⊢; tauto) (by simp), ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(K.vertex_ne_centroid ht htc hat).symm, hcw.symm⟩
    · simpa only [Finset.insert_comm] using hface
  have hvc := hedge v hv hve hvL
  have huc := hedge u hu hue huL
  have hcJ : c ∈ J.vertices := J.down_closed hvc (by simp) (by simp)
  exact (J.reachable_vertices_of_mem_face hvc ⟨v, hvJ⟩ ⟨c, hcJ⟩ (by simp) (by simp)).trans
    (J.reachable_vertices_of_mem_face huc ⟨c, hcJ⟩ ⟨u, huJ⟩ (by simp) (by simp))

omit [FiniteDimensional ℝ E] in


theorem closedFaceComplement_link_at_nonoriginal_centroid
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    {t : Finset E} (ht : t ∈ K.faces) (htc : 2 ≤ t.card)
    (hw : t.centroid ℝ id ∈ (K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).vertices) :
    IsConnected ((K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).link (t.centroid ℝ id)).space := by
  classical
  let C := K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)
  let w := t.centroid ℝ id
  let J := C.link w
  have hCpure := K.barycentricSubdivision.closedFaceComplement_pure
    (K.barycentricNeighborhood L) (K.barycentricSubdivision_pure_triangles hpure)
  have hnonempty : Nonempty J.vertices := by
    obtain ⟨q, hq, hqc, hwq⟩ := hCpure {w} hw
    have hwq' : w ∈ q := hwq (Finset.mem_singleton_self _)
    have hc : (q.erase w).card = 2 := by simp [Finset.card_erase_of_mem hwq', hqc]
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (q.erase w).card by omega)
    have hxt := Finset.mem_erase.mp hx
    exact ⟨⟨x, C.down_closed hq (Finset.singleton_subset_iff.mpr hxt.2) (by simp),
      by simpa only [Finset.mem_singleton] using hxt.1.symm,
      C.down_closed hq (by simpa only [Finset.insert_subset_iff,
        Finset.singleton_subset_iff] using And.intro hwq' hxt.2) (by simp)⟩⟩
  let : Nonempty J.vertices := hnonempty
  have hgraph : J.vertexAbstractComplex.edgeGraph.Connected := by
    refine ⟨?_⟩
    intro x y
    obtain ⟨v, hv, hvL, hvJ, hx⟩ := K.link_reaches_unmarked_vertex L hpure ht htc x
    obtain ⟨u, hu, huL, huJ, hy⟩ := K.link_reaches_unmarked_vertex L hpure ht htc y
    exact hx.trans ((K.unmarked_vertices_reachable L hpure ht htc hv hu hvL huL hvJ huJ).trans
      hy.symm)
  exact (J.isPathConnected_space_of_connected_edgeGraph hgraph).isConnected

omit [FiniteDimensional ℝ E] in


theorem closedFaceComplement_derived_links
    (L : SimplicialComplex ℝ E) (hLK : L ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space) :
    ∀ w ∈ (K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).vertices,
      IsConnected ((K.barycentricSubdivision.closedFaceComplement
        (K.barycentricNeighborhood L)).link w).space := by
  classical
  let C := K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)
  intro w hw
  obtain ⟨t, ht, htw⟩ := (K.mem_barycentricSubdivision_vertices_iff w).mp hw.1
  have hpos := (K.nonempty_of_mem_faces ht).card_pos
  by_cases ht1 : t.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp ht1
    have hvw : v = w := by simpa only [Finset.centroid_singleton, id_eq] using htw
    rw [← hvw] at hw ⊢
    have hvL : v ∉ L.vertices := by
      intro hvL
      let : Finite L.faces := (Set.Finite.subset (Set.toFinite K.faces) hLK).to_subtype
      exact disjoint_left.mp (K.closedFaceComplement_barycentric_disjoint L hLK)
        (C.subset_space hw (Finset.mem_singleton_self _))
        (L.subset_space hvL (Finset.mem_singleton_self _))
    rw [K.closedFaceComplement_link_at_original_vertex L hpure ht hvL]
    exact K.isConnected_barycentric_original_vertex_link ht (hlinks v ht)
  · subst w
    exact K.closedFaceComplement_link_at_nonoriginal_centroid L hpure ht (by omega) hw

end Geometry.SimplicialComplex
