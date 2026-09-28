import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTrianglePointwiseGluing
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleCofaceConstancy









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E)


def originalEdgeContact (s t : Triangle K) : Prop :=
  ∃ e ∈ K.faces, e.card = 2 ∧ e ⊆ s.val ∧ e ⊆ t.val

theorem pointwiseGlueRelation_of_common_vertex
    (label : Triangle K → ℝ)
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hlinks : ∀ v ∈ K.vertices,
      (K.faceLink {v}).vertexAbstractComplex.edgeGraph.Preconnected)
    {x y : carrier K label} {s t : Triangle K}
    (hxs : x.1 ∈ copy K label s) (hyt : y.1 ∈ copy K label t)
    (hvx : x.1.1 ∈ s.val) (hvy : x.1.1 ∈ t.val)
    (hxy : x.1.1 = y.1.1) :
    pointwiseGlueRelation K label (originalEdgeContact K) x y := by
  classical
  let v := x.1.1
  let P (q : Triangle K) : Prop := ∀ z : carrier K label,
    z.1 ∈ copy K label q → z.1.1 = v →
      pointwiseGlueRelation K label (originalEdgeContact K) x z
  have hvK : v ∈ K.vertices := K.down_closed s.property.1
    (Finset.singleton_subset_iff.mpr hvx) (Finset.singleton_nonempty _)
  have hstep (w : (K.faceLink {v}).vertices) (q r : Triangle K)
      (hwq : insert w.val {v} ⊆ q.val)
      (hwr : insert w.val {v} ⊆ r.val) : P q → P r := by
    intro hq z hzr hzv
    have hvq : v ∈ q.val := hwq (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    let u : carrier K label := ⟨(v, label q), mem_iUnion.mpr ⟨q,
      (mem_copy_iff K label q _).mpr ⟨subset_convexHull ℝ _ hvq, rfl⟩⟩⟩
    have huq : u.1 ∈ copy K label q := (mem_copy_iff K label q _).mpr
      ⟨subset_convexHull ℝ _ hvq, rfl⟩
    apply pointwiseGlueRelation_trans K label (originalEdgeContact K) (hq u huq rfl)
    apply Relation.EqvGen.rel
    refine ⟨q, r, huq, hzr, ?_, hzv.symm⟩
    refine ⟨insert w.val {v}, ?_, ?_, hwq, hwr⟩
    · simpa only [Finset.union_singleton] using w.property.2.2
    · rw [Finset.card_insert_of_notMem
        (K.faceLink_vertices_subset {v} w.property).2, Finset.card_singleton]
  have hPt : P s = P t := K.triangle_coface_constancy_of_link P hpure
    (s := {v}) (by simp) (hlinks v hvK)
    (fun w q r hq hr => propext ⟨hstep w q r hq hr, hstep w r q hr hq⟩)
    s t (Finset.singleton_subset_iff.mpr hvx) (Finset.singleton_subset_iff.mpr hvy)
  have hPs : P s := by
    intro z hzs hzv
    have hz : z = x := Subtype.ext
      (projection_injective_on_copy K label s hzs hxs hzv)
    subst z
    exact pointwiseGlueRelation_refl K label (originalEdgeContact K) x
  exact (hPt ▸ hPs) y hyt hxy.symm


theorem pointwiseGlueRelation_originalEdgeContact_iff
    (label : Triangle K → ℝ)
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hlinks : ∀ v ∈ K.vertices,
      (K.faceLink {v}).vertexAbstractComplex.edgeGraph.Preconnected)
    {x y : carrier K label} :
    pointwiseGlueRelation K label (originalEdgeContact K) x y ↔ x.1.1 = y.1.1 := by
  classical
  refine ⟨pointwiseGlueRelation_fiber K label _, ?_⟩
  intro hxy
  obtain ⟨s, hxs⟩ := mem_iUnion.mp x.2
  obtain ⟨t, hyt⟩ := mem_iUnion.mp y.2
  have hcommon : x.1.1 ∈ convexHull ℝ ((s.val ∩ t.val : Finset E) : Set E) := by
    simpa only [Finset.coe_inter] using collision_in_common_face K label hxs hyt hxy
  by_cases hcard : 2 ≤ (s.val ∩ t.val).card
  · obtain ⟨e, he, hecard⟩ := Finset.exists_subset_card_eq hcard
    have hes : e ⊆ s.val := he.trans Finset.inter_subset_left
    have het : e ⊆ t.val := he.trans Finset.inter_subset_right
    apply Relation.EqvGen.rel
    refine ⟨s, t, hxs, hyt, ⟨e, ?_, hecard, hes, het⟩, hxy⟩
    exact K.down_closed s.property.1 hes (Finset.card_pos.mp (by omega))
  · have hnonempty : (s.val ∩ t.val).Nonempty := by
      exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hcommon⟩)
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp
      (show (s.val ∩ t.val).card = 1 by have := hnonempty.card_pos; omega)
    have hxv : x.1.1 = v := by
      rw [hv, Finset.coe_singleton, convexHull_singleton] at hcommon
      exact hcommon
    apply pointwiseGlueRelation_of_common_vertex K label hpure hlinks hxs hyt
    · rw [hxv]
      exact Finset.mem_of_mem_inter_left (hv.symm ▸ Finset.mem_singleton_self v)
    · rw [hxv]
      exact Finset.mem_of_mem_inter_right (hv.symm ▸ Finset.mem_singleton_self v)
    · exact hxy


theorem pointwiseGlueRelation_originalEdgeContact_iff_of_connected_links
    (hK : K.faces.Finite) (label : Triangle K → ℝ)
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.faceLink {v}).space)
    {x y : carrier K label} :
    pointwiseGlueRelation K label (originalEdgeContact K) x y ↔ x.1.1 = y.1.1 := by
  apply pointwiseGlueRelation_originalEdgeContact_iff K label hpure
  intro v hv
  exact ((K.faceLink {v}).connected_edgeGraph_of_isConnected
    (SimplicialComplex.finite_faceLink_faces hK _) (hlinks v hv)).preconnected

end PoincareConjecture.M76.OriginalTriangleCopies
