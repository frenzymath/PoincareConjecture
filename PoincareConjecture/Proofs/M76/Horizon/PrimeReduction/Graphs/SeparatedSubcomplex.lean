import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (G : SimplicialComplex ℝ E) {A B : Set E}

omit [DecidableEq E] in
theorem convexHull_subset_of_closed_separation
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hcover : G.space ⊆ A ∪ B) {s : Finset E} (hs : s ∈ G.faces)
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) (hxA : x ∈ A) :
    convexHull ℝ (s : Set E) ⊆ A := by
  intro y hy
  rcases hcover (G.convexHull_subset_space hs hy) with hyA | hyB
  · exact hyA
  · obtain ⟨z, hz, hzA, hzB⟩ := isPreconnected_closed_iff.mp
      (convex_convexHull ℝ (s : Set E)).isPreconnected A B hA hB
      (fun z hz => hcover (G.convexHull_subset_space hs hz)) ⟨x, hx, hxA⟩ ⟨y, hy, hyB⟩
    exact False.elim (disjoint_left.mp hdis hzA hzB)

omit [DecidableEq E] in
theorem vertexSubcomplex_space_of_closed_separation
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hcover : G.space ⊆ A ∪ B) :
    (G.vertexSubcomplex A).space = G.space ∩ A := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨v, hv⟩ := G.nonempty_of_mem_faces hs.1
    exact ⟨G.convexHull_subset_space hs.1 hxs,
      G.convexHull_subset_of_closed_separation hA hB hdis hcover hs.1
        (subset_convexHull ℝ _ hv) (hs.2 v hv) hxs⟩
  · rintro ⟨hx, hxA⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    refine mem_space_iff.mpr ⟨s, ⟨hs, ?_⟩, hxs⟩
    intro v hv
    exact G.convexHull_subset_of_closed_separation hA hB hdis hcover hs hxs hxA
      (subset_convexHull ℝ _ hv)

omit [DecidableEq E] in
theorem vertexSubcomplex_coface_of_closed_separation
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hcover : G.space ⊆ A ∪ B) {s t : Finset E}
    (hs : s ∈ (G.vertexSubcomplex A).faces) (ht : t ∈ G.faces) (hst : s ⊆ t) :
    t ∈ (G.vertexSubcomplex A).faces := by
  obtain ⟨v, hv⟩ := G.nonempty_of_mem_faces hs.1
  refine ⟨ht, fun w hw => ?_⟩
  exact G.convexHull_subset_of_closed_separation hA hB hdis hcover ht
    (subset_convexHull ℝ _ (hst hv)) (hs.2 v hv) (subset_convexHull ℝ _ hw)

theorem vertexSubcomplex_vertex_link_of_closed_separation
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hcover : G.space ⊆ A ∪ B) {p : E} (hp : p ∈ (G.vertexSubcomplex A).vertices) :
    (G.vertexSubcomplex A).faceLink {p} = G.faceLink {p} := by
  apply SimplicialComplex.ext
  ext t
  change (t ∈ (G.vertexSubcomplex A).faces ∧ Disjoint {p} t ∧
      {p} ∪ t ∈ (G.vertexSubcomplex A).faces) ↔
    (t ∈ G.faces ∧ Disjoint {p} t ∧ {p} ∪ t ∈ G.faces)
  constructor
  · exact fun ht => ⟨ht.1.1, ht.2.1, ht.2.2.1⟩
  · intro ht
    have hcoface := G.vertexSubcomplex_coface_of_closed_separation hA hB hdis hcover
      hp ht.2.2 Finset.subset_union_left
    exact ⟨(G.vertexSubcomplex A).down_closed hcoface Finset.subset_union_right
      (G.nonempty_of_mem_faces ht.1), ht.2.1, hcoface⟩

theorem vertexSubcomplex_ncard_neighborSet_of_closed_separation
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hcover : G.space ⊆ A ∪ B) (v : (G.vertexSubcomplex A).vertices) :
    ((G.vertexSubcomplex A).vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
      (G.vertexAbstractComplex.edgeGraph.neighborSet
        ⟨v.val, G.vertexSubcomplex_le A v.property⟩).ncard := by
  rw [(G.vertexSubcomplex A).ncard_edgeGraph_neighborSet, G.ncard_edgeGraph_neighborSet,
    G.vertexSubcomplex_vertex_link_of_closed_separation hA hB hdis hcover v.property]

theorem exists_subcomplex_of_closed_image_partition
    {X : Type*} [TopologicalSpace X] (hG : G.faces.Finite)
    (f : E → X) (hf : ContinuousOn f G.space) {P Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q) (hdis : Disjoint P Q)
    (hcover : f '' G.space ⊆ P ∪ Q) :
    ∃ (H : SimplicialComplex ℝ E) (hHG : H ≤ G), H.faces.Finite ∧
      H.space = G.space ∩ f ⁻¹' P ∧ f '' H.space = (f '' G.space) ∩ P ∧
      ∀ v : H.vertices,
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
          (G.vertexAbstractComplex.edgeGraph.neighborSet
            ⟨v.val, hHG v.property⟩).ncard := by
  let A := G.space ∩ f ⁻¹' P
  let B := G.space ∩ f ⁻¹' Q
  have hAc : IsClosed A := hf.preimage_isClosed_of_isClosed
    (G.isCompact_space_of_finite hG).isClosed hP
  have hBc : IsClosed B := hf.preimage_isClosed_of_isClosed
    (G.isCompact_space_of_finite hG).isClosed hQ
  have hAB : Disjoint A B := disjoint_left.mpr fun _ hx hy =>
    disjoint_left.mp hdis hx.2 hy.2
  have hcov : G.space ⊆ A ∪ B := by
    intro x hx
    rcases hcover ⟨x, hx, rfl⟩ with hp | hq
    · exact Or.inl ⟨hx, hp⟩
    · exact Or.inr ⟨hx, hq⟩
  have hspace : (G.vertexSubcomplex A).space = G.space ∩ f ⁻¹' P := by
    rw [G.vertexSubcomplex_space_of_closed_separation hAc hBc hAB hcov]
    exact inter_eq_right.mpr inter_subset_left
  refine ⟨G.vertexSubcomplex A, G.vertexSubcomplex_le A,
    G.vertexSubcomplex_finite A hG, hspace, ?_, ?_⟩
  · rw [hspace, image_inter_preimage]
  · exact G.vertexSubcomplex_ncard_neighborSet_of_closed_separation hAc hBc hAB hcov

end Geometry.SimplicialComplex
