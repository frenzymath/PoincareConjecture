import PoincareConjecture.Proofs.M76.PrimeReduction.ActualArcComponents

set_option autoImplicit false

open Set

namespace SimpleGraph

theorem isCompact_segmentCarrier
    {V E : Type*} [Finite V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : SimpleGraph V) (p : V → E) : IsCompact (G.segmentCarrier p) := by
  have heq : G.segmentCarrier p = ⋃ v, ⋃ w, ⋃ (_ : G.Adj v w), segment ℝ (p v) (p w) := by
    ext x
    simp only [segmentCarrier, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [heq]
  apply isCompact_iUnion
  intro v
  apply isCompact_iUnion
  intro w
  apply isCompact_iUnion
  intro _
  simpa only [convexHull_pair] using (Set.toFinite ({p v, p w} : Set E)).isCompact_convexHull ℝ

end SimpleGraph

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem exists_open_component_neighborhood
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (hne : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃ U : Set E, IsOpen U ∧
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ⊆ U ∧
      G.space ∩ U = C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) := by
  classical
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  let H := G.vertexAbstractComplex.edgeGraph
  let carrier (D : H.ConnectedComponent) : Set E :=
    D.toSimpleGraph.segmentCarrier (fun v => (v.val : E))
  have hclosed (D : H.ConnectedComponent) : IsClosed (carrier D) :=
    (D.toSimpleGraph.isCompact_segmentCarrier (fun v => (v.val : E))).isClosed
  have hdis : Pairwise (fun D F => Disjoint (carrier D) (carrier F)) :=
    H.pairwise_disjoint_component_segmentCarrier ((↑) : G.vertices → E)
      Subtype.val_injective (fun {_ _ _ _} h h' => G.actual_edgeGraph_segment_intersection h h')
  have hwhole : G.space = ⋃ D, carrier D :=
    (G.actual_edgeGraph_segmentCarrier_eq_space hdim hne).symm.trans
      (H.segmentCarrier_eq_iUnion_components ((↑) : G.vertices → E))
  let other : Set E := ⋃ D : H.ConnectedComponent, ⋃ (_ : D ≠ C), carrier D
  have hother : IsClosed other := by
    apply isClosed_iUnion_of_finite
    intro D
    apply isClosed_iUnion_of_finite
    intro _
    exact hclosed D
  have hCU : carrier C ⊆ otherᶜ := by
    intro x hx hxother
    obtain ⟨D, hDC, hxD⟩ := mem_iUnion₂.mp hxother
    exact disjoint_left.mp (hdis hDC) hxD hx
  refine ⟨otherᶜ, hother.isOpen_compl, hCU, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hxG, hxU⟩
    obtain ⟨D, hxD⟩ := mem_iUnion.mp (hwhole.subset hxG)
    by_cases hDC : D = C
    · exact hDC ▸ hxD
    · exact (hxU (mem_iUnion₂.mpr ⟨D, hDC, hxD⟩)).elim
  · intro x hx
    exact ⟨hwhole.symm.subset (mem_iUnion.mpr ⟨C, hx⟩), hCU hx⟩

theorem exists_open_component_neighborhood_disjoint
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (hne : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {D : Set E} (hD : IsClosed D)
    (hCD : Disjoint (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E))) D) :
    ∃ U : Set E, IsOpen U ∧
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ⊆ U ∧
      G.space ∩ U = C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∧
      Disjoint U D := by
  obtain ⟨U, hU, hCU, hGU⟩ := G.exists_open_component_neighborhood hG hdim hne C
  refine ⟨U ∩ Dᶜ, hU.inter hD.isOpen_compl, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hCU hx, fun hxD => disjoint_left.mp hCD hx hxD⟩
  · apply Subset.antisymm
    · exact fun x hx => hGU.subset ⟨hx.1, hx.2.1⟩
    · intro x hx
      exact ⟨(hGU.symm.subset hx).1, hCU hx, fun hxD => disjoint_left.mp hCD hx hxD⟩
  · exact disjoint_left.mpr (fun _ hx hxD => hx.2 hxD)

end Geometry.SimplicialComplex
