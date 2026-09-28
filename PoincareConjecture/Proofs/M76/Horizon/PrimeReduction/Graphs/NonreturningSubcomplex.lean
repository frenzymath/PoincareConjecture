import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence









set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (G H : SimplicialComplex ℝ E)


theorem subcomplex_neighbor_image_of_ncard_eq (hG : G.faces.Finite) (hHG : H ≤ G)
    (v : H.vertices)
    (hdegree : (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
      (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val, hHG v.property⟩).ncard) :
    Subtype.val '' H.vertexAbstractComplex.edgeGraph.neighborSet v =
      Subtype.val '' G.vertexAbstractComplex.edgeGraph.neighborSet
        ⟨v.val, hHG v.property⟩ := by
  rw [H.image_edgeGraph_neighborSet, G.image_edgeGraph_neighborSet]
  have hlink : H.faceLink {v.val} ≤ G.faceLink {v.val} :=
    fun a ha => ⟨hHG ha.1, ha.2.1, hHG ha.2.2⟩
  have hvertices : (H.faceLink {v.val}).vertices ⊆ (G.faceLink {v.val}).vertices :=
    fun _ hx => hlink hx
  have hfinite : G.vertices.Finite := hG.preimage Finset.singleton_injective.injOn
  refine Set.eq_of_subset_of_ncard_le hvertices ?_ ?_
  · simpa only [H.ncard_edgeGraph_neighborSet, G.ncard_edgeGraph_neighborSet] using
      hdegree.ge
  · exact hfinite.subset fun _ hx => (G.faceLink_vertices_subset {v.val} hx).1


theorem subcomplex_component_of_ncard_eq (hG : G.faces.Finite) (hHG : H ≤ G)
    (hdegree : ∀ v : H.vertices,
      (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val, hHG v.property⟩).ncard)
    (D : H.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃ D₀ : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      Subtype.val '' D.supp = Subtype.val '' D₀.supp ∧
      Subtype.val '' {v : H.vertices | v ∈ D.supp ∧
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} =
      Subtype.val '' {v : G.vertices | v ∈ D₀.supp ∧
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} := by
  have hneighbor := G.subcomplex_neighbor_image_of_ncard_eq H hG hHG
  have hadj (v w : H.vertices) : H.vertexAbstractComplex.edgeGraph.Adj v w ↔
      G.vertexAbstractComplex.edgeGraph.Adj ⟨v.val, hHG v.property⟩
        ⟨w.val, hHG w.property⟩ := by
    constructor
    · intro h
      obtain ⟨z, hz, heq⟩ := (hneighbor v (hdegree v)).subset ⟨w, h, rfl⟩
      have heq' : z = ⟨w.val, hHG w.property⟩ := Subtype.ext heq
      exact heq' ▸ hz
    · intro h
      obtain ⟨z, hz, heq⟩ := (hneighbor v (hdegree v)).symm.subset
        ⟨⟨w.val, hHG w.property⟩, h, rfl⟩
      have heq' : z = w := Subtype.ext heq
      exact heq' ▸ hz
  let f : H.vertexAbstractComplex.edgeGraph →g G.vertexAbstractComplex.edgeGraph :=
    ⟨fun v => ⟨v.val, hHG v.property⟩, fun {v w} h => (hadj v w).mp h⟩
  have hclosed (v w : G.vertices) (hv : v.val ∈ H.vertices)
      (hvw : G.vertexAbstractComplex.edgeGraph.Adj v w) : w.val ∈ H.vertices := by
    obtain ⟨z, _, hz⟩ := (hneighbor ⟨v.val, hv⟩ (hdegree ⟨v.val, hv⟩)).symm.subset
      ⟨w, hvw, rfl⟩
    exact hz ▸ z.property
  have hreach (v w : G.vertices) (hr : G.vertexAbstractComplex.edgeGraph.Reachable v w) :
      v.val ∈ H.vertices → w.val ∈ H.vertices := by
    obtain ⟨p⟩ := hr
    induction p with
    | nil => exact id
    | @cons v z w hadj p ih => exact fun hv => ih (hclosed v z hv hadj)
  obtain ⟨v, hv⟩ := D.nonempty_supp
  let D₀ := G.vertexAbstractComplex.edgeGraph.connectedComponentMk (f v)
  have hv₀ : f v ∈ D₀.supp := rfl
  have hkeep (w : G.vertices) (hw : w ∈ D₀.supp) : w.val ∈ H.vertices :=
    hreach (f v) w (D₀.reachable_of_mem_supp hv₀ hw) v.property
  let back : D₀.toSimpleGraph →g H.vertexAbstractComplex.edgeGraph :=
    ⟨fun w => ⟨w.val.val, hkeep w.val w.property⟩,
      fun {w z} h => (hadj _ _).mpr h⟩
  have hmem (w : H.vertices) : w ∈ D.supp ↔ f w ∈ D₀.supp := by
    constructor
    · intro hw
      exact SimpleGraph.ConnectedComponent.sound ((D.reachable_of_mem_supp hw hv).map f)
    · intro hw
      have hr := (D₀.reachable_toSimpleGraph hw hv₀).map back
      have hr' : H.vertexAbstractComplex.edgeGraph.Reachable w v := hr
      exact (SimpleGraph.ConnectedComponent.sound hr').trans hv
  refine ⟨D₀, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨w, hw, rfl⟩
      exact ⟨f w, (hmem w).mp hw, rfl⟩
    · rintro x ⟨w, hw, rfl⟩
      exact ⟨⟨w.val, hkeep w hw⟩, (hmem _).mpr hw, rfl⟩
  · apply Subset.antisymm
    · rintro x ⟨w, hw, rfl⟩
      exact ⟨f w, ⟨(hmem w).mp hw.1, (hdegree w).symm.trans hw.2⟩, rfl⟩
    · rintro x ⟨w, hw, rfl⟩
      let w' : H.vertices := ⟨w.val, hkeep w hw.1⟩
      exact ⟨w', ⟨(hmem w').mpr hw.1, (hdegree w').trans hw.2⟩, rfl⟩


theorem no_return_to_of_subcomplex (hG : G.faces.Finite) (hHG : H ≤ G)
    (hdegree : ∀ v : H.vertices,
      (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val, hHG v.property⟩).ncard)
    (R : Set E)
    (h : ¬ ∃ D : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∃ v : D, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
      Subtype.val '' {v : G.vertices | v ∈ D.supp ∧
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆ R) :
    ¬ ∃ D : H.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∃ v : D, (H.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
      Subtype.val '' {v : H.vertices | v ∈ D.supp ∧
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆ R := by
  rintro ⟨D, ⟨v, hv⟩, hR⟩
  obtain ⟨D₀, _, heq⟩ := G.subcomplex_component_of_ncard_eq H hG hHG hdegree D
  have hvimage : (v.val : E) ∈ Subtype.val '' {w : G.vertices | w ∈ D₀.supp ∧
      (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1} :=
    heq.subset ⟨v.val, ⟨v.property, hv⟩, rfl⟩
  obtain ⟨w, hw, _⟩ := hvimage
  exact h ⟨D₀, ⟨⟨w, hw.1⟩, hw.2⟩, heq ▸ hR⟩


theorem nonreturning_of_subcomplex
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hG : G.faces.Finite) (hHG : H ≤ G)
    (hdegree : ∀ v : H.vertices,
      (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val, hHG v.property⟩).ncard)
    (s : Finset F) (A : F →ᴬ[ℝ] E)
    (h : ∀ a : Finset F, a ⊆ s → a.card = 2 →
      ¬ ∃ D : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (∃ v : D, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ D.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set F))) :
    ∀ a : Finset F, a ⊆ s → a.card = 2 →
      ¬ ∃ D : H.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (∃ v : D, (H.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : H.vertices | v ∈ D.supp ∧
          (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set F)) := by
  intro a ha hac
  exact G.no_return_to_of_subcomplex H hG hHG hdegree _ (h a ha hac)

end Geometry.SimplicialComplex
