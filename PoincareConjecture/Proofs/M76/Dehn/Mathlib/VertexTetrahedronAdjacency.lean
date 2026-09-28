import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronAdjacency









set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)




noncomputable def vertexFaceEquiv (n : ℕ) :
    {s : Finset K.vertices // s ∈ K.vertexAbstractComplex.faces ∧ s.card = n} ≃
      {s : Finset E // s ∈ K.faces ∧ s.card = n} := by
  classical
  let emb : K.vertices ↪ E := Function.Embedding.subtype _
  let f : {s : Finset K.vertices // s ∈ K.vertexAbstractComplex.faces ∧ s.card = n} →
      {s : Finset E // s ∈ K.faces ∧ s.card = n} := fun s =>
    ⟨s.val.map emb, s.property.1, by simpa only [Finset.card_map] using s.property.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro s t h
    exact Subtype.ext (Finset.map_injective emb (congrArg Subtype.val h))
  · intro t
    have hv (x : E) (hx : x ∈ t.val) : x ∈ K.vertices :=
      K.down_closed t.property.1 (Finset.singleton_subset_iff.mpr hx)
        (Finset.singleton_nonempty x)
    let s : Finset K.vertices := t.val.subtype (fun x => x ∈ K.vertices)
    have hmap : s.map emb = t.val := Finset.subtype_map_of_mem hv
    have hs : s ∈ K.vertexAbstractComplex.faces := by
      change s.map emb ∈ K.faces
      rw [hmap]
      exact t.property.1
    have hsc : s.card = n := by
      rw [← Finset.card_map emb, hmap]
      exact t.property.2
    exact ⟨⟨s, hs, hsc⟩, Subtype.ext hmap⟩



theorem vertexFaceEquiv_map (n : ℕ)
    (s : {s : Finset K.vertices // s ∈ K.vertexAbstractComplex.faces ∧ s.card = n}) :
    (K.vertexFaceEquiv n s).val = s.val.map (Function.Embedding.subtype _) := rfl



theorem vertexFaceEquiv_symm_map (n : ℕ)
    (s : {s : Finset E // s ∈ K.faces ∧ s.card = n}) :
    ((K.vertexFaceEquiv n).symm s).val.map (Function.Embedding.subtype _) = s.val :=
  congrArg Subtype.val ((K.vertexFaceEquiv n).apply_symm_apply s)

open Classical in



theorem vertexFaceEquiv_symm_val (n : ℕ)
    (s : {s : Finset E // s ∈ K.faces ∧ s.card = n}) :
    ((K.vertexFaceEquiv n).symm s).val = s.val.subtype (fun x => x ∈ K.vertices) := by
  apply Finset.map_injective (Function.Embedding.subtype _)
  rw [K.vertexFaceEquiv_symm_map]
  symm
  apply Finset.subtype_map_of_mem
  intro x hx
  exact K.down_closed s.property.1 (Finset.singleton_subset_iff.mpr hx)
    (Finset.singleton_nonempty x)




theorem vertex_tetrahedronGraph_connected
    (hconn : (tetrahedronGraph K.toPreAbstractSimplicialComplex).Connected) :
    (tetrahedronGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex).Connected := by
  let e := K.vertexFaceEquiv 4
  let f : tetrahedronGraph K.toPreAbstractSimplicialComplex →g
      tetrahedronGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex := {
    toFun := e.symm
    map_rel' := by
      intro q r hqr
      obtain ⟨hne, t, htq, htr⟩ := hqr
      refine ⟨fun h => hne (e.symm.injective h), (K.vertexFaceEquiv 3).symm t, ?_, ?_⟩
      · apply Finset.map_subset_map.mp
        change ((K.vertexFaceEquiv 3).symm t).val.map (Function.Embedding.subtype _) ⊆
          ((K.vertexFaceEquiv 4).symm q).val.map (Function.Embedding.subtype _)
        rw [K.vertexFaceEquiv_symm_map, K.vertexFaceEquiv_symm_map]
        exact htq
      · apply Finset.map_subset_map.mp
        change ((K.vertexFaceEquiv 3).symm t).val.map (Function.Embedding.subtype _) ⊆
          ((K.vertexFaceEquiv 4).symm r).val.map (Function.Embedding.subtype _)
        rw [K.vertexFaceEquiv_symm_map, K.vertexFaceEquiv_symm_map]
        exact htr }
  exact hconn.map f e.symm.surjective

end Geometry.SimplicialComplex
