import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.NonreturningSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.GeometricGraphComponents

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (G H : SimplicialComplex ℝ E)

theorem subcomplex_component_segmentCarrier_of_ncard_eq
    (hG : G.faces.Finite) (hHG : H ≤ G)
    (hdegree : ∀ v : H.vertices,
      (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val, hHG v.property⟩).ncard)
    (D : H.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃ D₀ : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      Subtype.val '' D.supp = Subtype.val '' D₀.supp ∧
      D.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) =
        D₀.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) := by
  obtain ⟨D₀, hsupp, _⟩ := G.subcomplex_component_of_ncard_eq H hG hHG hdegree D
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
  have hmem (v : H.vertices) (hv : v ∈ D.supp) :
      (⟨v.val, hHG v.property⟩ : G.vertices) ∈ D₀.supp := by
    obtain ⟨w, hw, heq⟩ := hsupp.subset ⟨v, hv, rfl⟩
    have heq' : w = ⟨v.val, hHG v.property⟩ := Subtype.ext heq
    exact heq' ▸ hw
  refine ⟨D₀, hsupp, ?_⟩
  ext x
  constructor
  · rintro ⟨v, w, hvw, hx⟩
    exact ⟨⟨⟨v.val.val, hHG v.val.property⟩, hmem v.val v.property⟩,
      ⟨⟨w.val.val, hHG w.val.property⟩, hmem w.val w.property⟩,
      (hadj v.val w.val).mp hvw, hx⟩
  · rintro ⟨v, w, hvw, hx⟩
    obtain ⟨v', hv', hvEq⟩ := hsupp.symm.subset ⟨v.val, v.property, rfl⟩
    obtain ⟨w', hw', hwEq⟩ := hsupp.symm.subset ⟨w.val, w.property, rfl⟩
    have hvG : (⟨v'.val, hHG v'.property⟩ : G.vertices) = v.val := Subtype.ext hvEq
    have hwG : (⟨w'.val, hHG w'.property⟩ : G.vertices) = w.val := Subtype.ext hwEq
    refine ⟨⟨v', hv'⟩, ⟨w', hw'⟩, (hadj v' w').mpr ?_, ?_⟩
    · rw [hvG, hwG]
      exact hvw
    · change x ∈ segment ℝ v'.val w'.val
      simpa only [hvEq, hwEq] using hx

theorem component_segmentCarrier_meets_of_subcomplex
    (hG : G.faces.Finite) (hHG : H ≤ G)
    (hdegree : ∀ v : H.vertices,
      (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val, hHG v.property⟩).ncard)
    (R : Set E)
    (h : ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩ R).Nonempty) :
    ∀ D : H.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (D.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩ R).Nonempty := by
  intro D
  obtain ⟨D₀, _, heq⟩ :=
    G.subcomplex_component_segmentCarrier_of_ncard_eq H hG hHG hdegree D
  rw [heq]
  exact h D₀

end Geometry.SimplicialComplex
