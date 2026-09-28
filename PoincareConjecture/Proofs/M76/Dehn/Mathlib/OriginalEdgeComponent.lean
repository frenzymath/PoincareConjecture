import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

def edgeComponentComplex (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    SimplicialComplex ℝ E := K.vertexSubcomplex (Subtype.val '' C.supp)

theorem edgeComponentComplex_le (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    K.edgeComponentComplex C ≤ K := K.vertexSubcomplex_le _

theorem edgeComponentComplex_vertex_iff
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) (p : K.vertices) :
    p.val ∈ (K.edgeComponentComplex C).vertices ↔ p ∈ C.supp := by
  rw [edgeComponentComplex, K.vertexSubcomplex_vertices]
  simp only [mem_inter_iff, p.property, true_and, Subtype.val_injective.mem_set_image]

theorem edge_component_face_vertex
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {t : Finset E} (ht : t ∈ K.faces) {p q : K.vertices}
    (hp : p.val ∈ t) (hq : q.val ∈ t) (hpC : p ∈ C.supp) : q ∈ C.supp := by
  by_cases hpq : p = q
  · exact hpq ▸ hpC
  · apply C.mem_supp_of_adj_mem_supp hpC
    refine ⟨hpq, ?_⟩
    change ({p, q} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
    simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
    apply K.down_closed ht
      (Finset.insert_subset_iff.mpr ⟨hp, Finset.singleton_subset_iff.mpr hq⟩)
    exact Finset.insert_nonempty _ _

theorem edgeComponentComplex_coface
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {s t : Finset E} (hs : s ∈ (K.edgeComponentComplex C).faces)
    (ht : t ∈ K.faces) (hst : s ⊆ t) : t ∈ (K.edgeComponentComplex C).faces := by
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs.1
  obtain ⟨p0, hpC, hpp⟩ := hs.2 p hps
  have hp0t : p0.val ∈ t := hpp.symm ▸ hst hps
  refine ⟨ht, ?_⟩
  intro q hqt
  have hqK : q ∈ K.vertices := K.down_closed ht
    (Finset.singleton_subset_iff.mpr hqt) (Finset.singleton_nonempty q)
  exact ⟨⟨q, hqK⟩, K.edge_component_face_vertex C ht hp0t hqt hpC, rfl⟩

theorem edgeComponentComplex_cofaces
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {s : Finset E} (hs : s ∈ (K.edgeComponentComplex C).faces) (n : ℕ) :
    {t : Finset E | t ∈ (K.edgeComponentComplex C).faces ∧ t.card = n ∧ s ⊆ t} =
      {t : Finset E | t ∈ K.faces ∧ t.card = n ∧ s ⊆ t} := by
  ext t
  constructor
  · intro ht
    exact ⟨ht.1.1, ht.2⟩
  · intro ht
    exact ⟨K.edgeComponentComplex_coface C hs ht.1 ht.2.2, ht.2⟩

theorem edgeComponentComplex_pure
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) {n : ℕ}
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = n) :
    ∀ s ∈ (K.edgeComponentComplex C).faces,
      ∃ t ∈ (K.edgeComponentComplex C).faces, s ⊆ t ∧ t.card = n := by
  intro s hs
  obtain ⟨t, ht, hst, hcard⟩ := hpure s hs.1
  exact ⟨t, K.edgeComponentComplex_coface C hs ht hst, hst, hcard⟩

theorem edgeComponentComplex_vertex_link
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {p : E} (hp : p ∈ (K.edgeComponentComplex C).vertices) :
    (K.edgeComponentComplex C).faceLink {p} = K.faceLink {p} := by
  apply SimplicialComplex.ext
  ext t
  change (t ∈ (K.edgeComponentComplex C).faces ∧ Disjoint {p} t ∧
      {p} ∪ t ∈ (K.edgeComponentComplex C).faces) ↔
    (t ∈ K.faces ∧ Disjoint {p} t ∧ {p} ∪ t ∈ K.faces)
  constructor
  · intro ht
    exact ⟨ht.1.1, ht.2.1, ht.2.2.1⟩
  · intro ht
    have hcoface : {p} ∪ t ∈ (K.edgeComponentComplex C).faces :=
      K.edgeComponentComplex_coface C hp ht.2.2 Finset.subset_union_left
    have htC : t ∈ (K.edgeComponentComplex C).faces :=
      (K.edgeComponentComplex C).down_closed hcoface Finset.subset_union_right
        (K.nonempty_of_mem_faces ht.1)
    exact ⟨htC, ht.2.1, hcoface⟩

end Geometry.SimplicialComplex
