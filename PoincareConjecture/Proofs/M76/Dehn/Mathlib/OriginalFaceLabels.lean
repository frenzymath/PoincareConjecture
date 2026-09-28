import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BarycentricEdgeLabels










set_option autoImplicit false

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)



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



theorem allVertexFacesEquiv_apply_val (s : K.vertexAbstractComplex.faces) :
    (K.allVertexFacesEquiv s).val = s.val.map (Function.Embedding.subtype _) := rfl



theorem allVertexFacesEquiv_subset_iff (s t : K.vertexAbstractComplex.faces) :
    (K.allVertexFacesEquiv s).val ⊆ (K.allVertexFacesEquiv t).val ↔ s.val ⊆ t.val :=
  Finset.map_subset_map



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



noncomputable def vertexFaceCentroidGraphIso :
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex.faceInclusionGraph ≃g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph :=
  K.vertexFaceGraphIso.trans K.faceCentroidGraphIso

end Geometry.SimplicialComplex
