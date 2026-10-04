import PoincareLib.Topology.Manifold.Smoothing.Dehn.Barycentric.Mathlib.BarycentricEdgeLabels

/-!
# Whole original face labels on the actual vertex type

Forgetting the vertex subtype bijects the faces of the actual vertex
complex with the original geometric faces. It preserves full inclusion
and gives the literal face-label graph of the centroid subdivision.
See Putman, Theorem 5.1, pp. 15--16, and Dehn derivation 021, section 1.
-/

set_option autoImplicit false

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

/-- Forgetting the actual vertex subtype bijects the entire original
face collections. See Dehn derivation 021, section 1. -/
noncomputable def allVertexFacesEquiv : K.vertexAbstractComplex.faces ≃ K.faces :=
  Equiv.ofBijective
    (fun s => ⟨s.val.map (Function.Embedding.subtype _), s.property⟩)
    ⟨fun _ _ h => Subtype.ext
      (Finset.map_injective (Function.Embedding.subtype _) (congrArg Subtype.val h)), by
      intro t
      have ht : ∃ s ∈ K.vertexAbstractComplex.faces,
          (t.val : Set E) = Subtype.val '' (s : Set K.vertices) :=
        K.faces_eq_vertexAbstractComplex_images.subset t.property
      obtain ⟨s, hs, he⟩ := ht
      refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
      apply Finset.coe_injective
      simpa only [Finset.coe_map, Function.Embedding.coe_subtype] using he.symm⟩

/-- The original face-label equivalence retains every actual vertex.
See Dehn derivation 021, section 1. -/
theorem allVertexFacesEquiv_apply_val (s : K.vertexAbstractComplex.faces) :
    (K.allVertexFacesEquiv s).val = s.val.map (Function.Embedding.subtype _) := rfl

/-- The label equivalence preserves the entire inclusion relation,
not just face cardinality. See Dehn derivation 021, section 1. -/
theorem allVertexFacesEquiv_subset_iff (s t : K.vertexAbstractComplex.faces) :
    (K.allVertexFacesEquiv s).val ⊆ (K.allVertexFacesEquiv t).val ↔ s.val ⊆ t.val :=
  Finset.map_subset_map

/-- The two full original face-inclusion graphs are isomorphic by
forgetting only the vertex subtype. See Dehn derivation 021, section 1. -/
noncomputable def vertexFaceGraphIso :
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex.faceInclusionGraph ≃g
      K.toPreAbstractSimplicialComplex.faceInclusionGraph where
  toEquiv := K.allVertexFacesEquiv
  map_rel_iff' := by
    intro s t
    change (K.allVertexFacesEquiv s ≠ K.allVertexFacesEquiv t ∧
      ((K.allVertexFacesEquiv s).val ⊆ (K.allVertexFacesEquiv t).val ∨
        (K.allVertexFacesEquiv t).val ⊆ (K.allVertexFacesEquiv s).val)) ↔
      s ≠ t ∧ (s.val ⊆ t.val ∨ t.val ⊆ s.val)
    rw [K.allVertexFacesEquiv.injective.ne_iff, K.allVertexFacesEquiv_subset_iff,
      K.allVertexFacesEquiv_subset_iff]

variable [Fintype K.faces] [DecidableEq E]

/-- The actual original vertex-face labels identify the whole centroid
edge graph with the whole face-inclusion graph. See Dehn 021, section 1. -/
noncomputable def vertexFaceCentroidGraphIso :
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex.faceInclusionGraph ≃g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph :=
  K.vertexFaceGraphIso.trans K.faceCentroidGraphIso

end Geometry.SimplicialComplex
