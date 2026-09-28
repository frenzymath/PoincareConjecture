import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalEdgeComponent
import PoincareConjecture.Proofs.M76.PrimeReduction.ActualGraphCarrier
import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence










set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (G : SimplicialComplex ℝ E)


def deleteEdgeComponent (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    SimplicialComplex ℝ E := G.vertexSubcomplex (Subtype.val '' C.supp)ᶜ

theorem deleteEdgeComponent_le
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    G.deleteEdgeComponent C ≤ G := G.vertexSubcomplex_le _

theorem deleteEdgeComponent_finite
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) (hG : G.faces.Finite) :
    (G.deleteEdgeComponent C).faces.Finite :=
  G.vertexSubcomplex_finite _ hG

theorem deleteEdgeComponent_vertex_iff
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) (v : G.vertices) :
    v.val ∈ (G.deleteEdgeComponent C).vertices ↔ v ∉ C.supp := by
  rw [deleteEdgeComponent, G.vertexSubcomplex_vertices]
  simp only [mem_inter_iff, v.property, true_and, mem_compl_iff,
    Subtype.val_injective.mem_set_image]


theorem deleteEdgeComponent_coface
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {s t : Finset E} (hs : s ∈ (G.deleteEdgeComponent C).faces)
    (ht : t ∈ G.faces) (hst : s ⊆ t) : t ∈ (G.deleteEdgeComponent C).faces := by
  obtain ⟨p, hps⟩ := G.nonempty_of_mem_faces hs.1
  have hpG : p ∈ G.vertices := G.face_subset_vertices hs.1 hps
  refine ⟨ht, ?_⟩
  intro q hqt hqC
  obtain ⟨q0, hq0, rfl⟩ := hqC
  have hpC : (⟨p, hpG⟩ : G.vertices) ∈ C.supp :=
    G.edge_component_face_vertex C ht hqt (hst hps) hq0
  exact hs.2 p hps ⟨⟨p, hpG⟩, hpC, rfl⟩

theorem deleteEdgeComponent_cofaces
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {s : Finset E} (hs : s ∈ (G.deleteEdgeComponent C).faces) (n : ℕ) :
    {t : Finset E | t ∈ (G.deleteEdgeComponent C).faces ∧ t.card = n ∧ s ⊆ t} =
      {t : Finset E | t ∈ G.faces ∧ t.card = n ∧ s ⊆ t} := by
  ext t
  exact ⟨fun ht => ⟨ht.1.1, ht.2⟩,
    fun ht => ⟨G.deleteEdgeComponent_coface C hs ht.1 ht.2.2, ht.2⟩⟩

theorem deleteEdgeComponent_vertex_link
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {p : E} (hp : p ∈ (G.deleteEdgeComponent C).vertices) :
    (G.deleteEdgeComponent C).faceLink {p} = G.faceLink {p} := by
  apply SimplicialComplex.ext
  ext t
  change (t ∈ (G.deleteEdgeComponent C).faces ∧ Disjoint {p} t ∧
      {p} ∪ t ∈ (G.deleteEdgeComponent C).faces) ↔
    (t ∈ G.faces ∧ Disjoint {p} t ∧ {p} ∪ t ∈ G.faces)
  constructor
  · exact fun ht => ⟨ht.1.1, ht.2.1, ht.2.2.1⟩
  · intro ht
    have hcoface := G.deleteEdgeComponent_coface C hp ht.2.2 Finset.subset_union_left
    exact ⟨(G.deleteEdgeComponent C).down_closed hcoface Finset.subset_union_right
      (G.nonempty_of_mem_faces ht.1), ht.2.1, hcoface⟩


theorem deleteEdgeComponent_neighbor_image
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (v : (G.deleteEdgeComponent C).vertices) :
    Subtype.val '' (G.deleteEdgeComponent C).vertexAbstractComplex.edgeGraph.neighborSet v =
      Subtype.val '' G.vertexAbstractComplex.edgeGraph.neighborSet
        ⟨v.val, G.deleteEdgeComponent_le C v.property⟩ := by
  rw [(G.deleteEdgeComponent C).image_edgeGraph_neighborSet, G.image_edgeGraph_neighborSet,
    G.deleteEdgeComponent_vertex_link C v.property]

theorem deleteEdgeComponent_ncard_neighborSet
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (v : (G.deleteEdgeComponent C).vertices) :
    ((G.deleteEdgeComponent C).vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
      (G.vertexAbstractComplex.edgeGraph.neighborSet
        ⟨v.val, G.deleteEdgeComponent_le C v.property⟩).ncard := by
  rw [(G.deleteEdgeComponent C).ncard_edgeGraph_neighborSet, G.ncard_edgeGraph_neighborSet,
    G.deleteEdgeComponent_vertex_link C v.property]

theorem deleteEdgeComponent_no_isolated_vertices
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hne : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty) :
    ∀ v : (G.deleteEdgeComponent C).vertices,
      ((G.deleteEdgeComponent C).vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty := by
  intro v
  have h := (hne ⟨v.val, G.deleteEdgeComponent_le C v.property⟩).image Subtype.val
  rw [← G.deleteEdgeComponent_neighbor_image C v] at h
  exact h.of_image

theorem deleteEdgeComponent_face_card_le
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hdim : ∀ s ∈ G.faces, s.card ≤ 2) :
    ∀ s ∈ (G.deleteEdgeComponent C).faces, s.card ≤ 2 :=
  fun s hs => hdim s hs.1


theorem deleteEdgeComponent_space
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (hne : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty) :
    (G.deleteEdgeComponent C).space =
      G.space \ C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) := by
  have hedge {v w : G.vertices} (h : G.vertexAbstractComplex.edgeGraph.Adj v w) :
      ({v.val, w.val} : Finset E) ∈ G.faces := by
    have hh := h.2
    change ({v, w} : Finset G.vertices).map (Function.Embedding.subtype _) ∈ G.faces at hh
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
      using hh
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    refine ⟨G.convexHull_subset_space hs.1 hxs, ?_⟩
    rintro ⟨v, w, hvw, hxvw⟩
    have hempty : (s : Set E) ∩ {(v.val : E), (w.val : E)} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      rcases hy.2 with hv | hw
      · exact hs.2 y hy.1 ⟨v.val, v.property, hv.symm⟩
      · exact hs.2 y hy.1 ⟨w.val, w.property, hw.symm⟩
    have hface : ({(v.val : E), (w.val : E)} : Finset E) ∈ G.faces :=
      hedge (v := v.val) (w := w.val) hvw
    have hinter := G.inter_subset_convexHull hs.1 hface ⟨hxs, by
      simpa only [Finset.coe_pair, convexHull_pair] using hxvw⟩
    simp only [Finset.coe_pair, hempty, convexHull_empty, notMem_empty] at hinter
  · rintro x ⟨hxG, hxC⟩
    obtain ⟨v, w, hvw, hxvw⟩ :=
      (G.actual_edgeGraph_segmentCarrier_eq_space hdim hne).symm.subset hxG
    have hvC : v ∉ C.supp := by
      intro hv
      exact hxC ⟨⟨v, hv⟩, ⟨w, C.mem_supp_of_adj_mem_supp hv hvw⟩, hvw, hxvw⟩
    have hvkeep : v.val ∈ (G.deleteEdgeComponent C).vertices :=
      (G.deleteEdgeComponent_vertex_iff C v).mpr hvC
    have hkeep : ({v.val, w.val} : Finset E) ∈ (G.deleteEdgeComponent C).faces :=
      G.deleteEdgeComponent_coface C hvkeep (hedge hvw)
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
    apply (G.deleteEdgeComponent C).convexHull_subset_space hkeep
    simpa only [Finset.coe_pair, convexHull_pair] using hxvw


theorem deleteEdgeComponent_faces_ncard_lt
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) (hG : G.faces.Finite) :
    (G.deleteEdgeComponent C).faces.ncard < G.faces.ncard := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  apply Set.ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨G.deleteEdgeComponent_le C, ?_⟩) hG
  intro heq
  change (G.deleteEdgeComponent C).faces = G.faces at heq
  have hkeep : v.val ∈ (G.deleteEdgeComponent C).vertices := by
    change {v.val} ∈ (G.deleteEdgeComponent C).faces
    rw [heq]
    exact v.property
  exact (G.deleteEdgeComponent_vertex_iff C v).mp hkeep hv

end Geometry.SimplicialComplex
