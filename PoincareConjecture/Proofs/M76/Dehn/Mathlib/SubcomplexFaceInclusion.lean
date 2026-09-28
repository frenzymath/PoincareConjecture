import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts

set_option autoImplicit false

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K A : SimplicialComplex ℝ E)

def subcomplexVertexEmbedding (hAK : A ≤ K) : A.vertices ↪ K.vertices where
  toFun p := ⟨p.val, hAK p.property⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z : K.vertices => z.val) h

noncomputable def subcomplexFaceEmbedding (hAK : A ≤ K) (n : ℕ) :
    {s : Finset A.vertices // s ∈ A.vertexAbstractComplex.faces ∧ s.card = n} ↪
      {s : Finset K.vertices // s ∈ K.vertexAbstractComplex.faces ∧ s.card = n} where
  toFun s := ⟨s.val.map (K.subcomplexVertexEmbedding A hAK), by
    change (s.val.map (K.subcomplexVertexEmbedding A hAK)).map
      (Function.Embedding.subtype _) ∈ K.faces
    rw [Finset.map_map]
    exact hAK s.property.1,
    by simpa only [Finset.card_map] using s.property.2⟩
  inj' := fun _ _ h => Subtype.ext
    (Finset.map_injective (K.subcomplexVertexEmbedding A hAK) (congrArg Subtype.val h))

theorem subcomplexFaceEmbedding_map (hAK : A ≤ K) (n : ℕ)
    (s : {s : Finset A.vertices // s ∈ A.vertexAbstractComplex.faces ∧ s.card = n}) :
    (K.subcomplexFaceEmbedding A hAK n s).val =
      s.val.map (K.subcomplexVertexEmbedding A hAK) := rfl

theorem subcomplexFaceEmbedding_forget (hAK : A ≤ K) (n : ℕ)
    (s : {s : Finset A.vertices // s ∈ A.vertexAbstractComplex.faces ∧ s.card = n}) :
    (K.subcomplexFaceEmbedding A hAK n s).val.map (Function.Embedding.subtype _) =
      s.val.map (Function.Embedding.subtype _) := by
  rw [K.subcomplexFaceEmbedding_map, Finset.map_map]
  rfl

theorem subcomplexFaceEmbedding_range_iff (hAK : A ≤ K) (n : ℕ)
    (s : {s : Finset K.vertices // s ∈ K.vertexAbstractComplex.faces ∧ s.card = n}) :
    s ∈ Set.range (K.subcomplexFaceEmbedding A hAK n) ↔
      s.val.map (Function.Embedding.subtype _) ∈ A.faces := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [K.subcomplexFaceEmbedding_forget]
    exact t.property.1
  · intro hs
    let a : A.FaceOfCard n := ⟨s.val.map (Function.Embedding.subtype _), hs,
      by simpa only [Finset.card_map] using s.property.2⟩
    let t := (A.vertexFaceEquiv n).symm a
    refine ⟨t, Subtype.ext ?_⟩
    apply Finset.map_injective (Function.Embedding.subtype _)
    rw [K.subcomplexFaceEmbedding_forget]
    exact A.vertexFaceEquiv_symm_map n a

theorem subcomplexFaceEmbedding_subset_iff (hAK : A ≤ K) {n m : ℕ}
    (s : {s : Finset A.vertices // s ∈ A.vertexAbstractComplex.faces ∧ s.card = n})
    (t : {s : Finset A.vertices // s ∈ A.vertexAbstractComplex.faces ∧ s.card = m}) :
    (K.subcomplexFaceEmbedding A hAK n s).val ⊆
        (K.subcomplexFaceEmbedding A hAK m t).val ↔ s.val ⊆ t.val := by
  rw [K.subcomplexFaceEmbedding_map, K.subcomplexFaceEmbedding_map]
  exact Finset.map_subset_map

theorem exists_unique_subcomplex_lower_face (hAK : A ≤ K) {n m : ℕ}
    (s : {s : Finset K.vertices // s ∈ K.vertexAbstractComplex.faces ∧ s.card = n})
    (t : {s : Finset A.vertices // s ∈ A.vertexAbstractComplex.faces ∧ s.card = m})
    (hst : s.val ⊆ (K.subcomplexFaceEmbedding A hAK m t).val) :
    ∃! u : {s : Finset A.vertices // s ∈ A.vertexAbstractComplex.faces ∧ s.card = n},
      K.subcomplexFaceEmbedding A hAK n u = s ∧ u.val ⊆ t.val := by
  have hgeom : s.val.map (Function.Embedding.subtype _) ⊆
      (K.subcomplexFaceEmbedding A hAK m t).val.map (Function.Embedding.subtype _) :=
    Finset.map_subset_map.mpr hst
  rw [K.subcomplexFaceEmbedding_forget] at hgeom
  have hmark : s.val.map (Function.Embedding.subtype _) ∈ A.faces :=
    A.down_closed t.property.1 hgeom (K.nonempty_of_mem_faces s.property.1)
  obtain ⟨u, hu⟩ := (K.subcomplexFaceEmbedding_range_iff A hAK n s).mpr hmark
  refine ⟨u, ⟨hu, ?_⟩, ?_⟩
  · apply (K.subcomplexFaceEmbedding_subset_iff A hAK u t).mp
    rw [hu]
    exact hst
  · intro v hv
    exact (K.subcomplexFaceEmbedding A hAK n).injective (hv.1.trans hu.symm)

end Geometry.SimplicialComplex
