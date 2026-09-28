import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleAdjacency
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleChainCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTetrahedronAdjacency








set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)



theorem vertex_triangleGraph_connected
    (hconn : (triangleGraph K.toPreAbstractSimplicialComplex).Connected) :
    (triangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex).Connected := by
  let e := K.vertexFaceEquiv 3
  let f : triangleGraph K.toPreAbstractSimplicialComplex →g
      triangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex := {
    toFun := e.symm
    map_rel' := by
      intro q r hqr
      obtain ⟨hne, t, htq, htr⟩ := hqr
      refine ⟨fun h => hne (e.symm.injective h), (K.vertexFaceEquiv 2).symm t, ?_, ?_⟩
      · apply Finset.map_subset_map.mp
        change ((K.vertexFaceEquiv 2).symm t).val.map (Function.Embedding.subtype _) ⊆
          ((K.vertexFaceEquiv 3).symm q).val.map (Function.Embedding.subtype _)
        rw [K.vertexFaceEquiv_symm_map, K.vertexFaceEquiv_symm_map]
        exact htq
      · apply Finset.map_subset_map.mp
        change ((K.vertexFaceEquiv 2).symm t).val.map (Function.Embedding.subtype _) ⊆
          ((K.vertexFaceEquiv 3).symm r).val.map (Function.Embedding.subtype _)
        rw [K.vertexFaceEquiv_symm_map, K.vertexFaceEquiv_symm_map]
        exact htr }
  exact hconn.map f e.symm.surjective




theorem triangleCofaces_card_eq_original [Fintype K.vertices]
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    (triangleCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex e).card =
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧
        e.val.map (Function.Embedding.subtype _) ⊆ t}.ncard := by
  classical
  let : DecidableEq K.vertices := Classical.decEq K.vertices
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let emb : K.vertices ↪ E := Function.Embedding.subtype _
  rw [← ncard_coe_finset (triangleCofaces A e)]
  apply ncard_congr (fun t _ => t.val.map emb)
  · intro t ht
    have hsub : e.val ⊆ t.val := (Finset.mem_filter.mp ht).2
    refine ⟨t.property.1, ?_, Finset.map_subset_map.mpr hsub⟩
    simpa only [Finset.card_map] using t.property.2
  · intro q r _ _ hqr
    exact Subtype.ext (Finset.map_injective emb hqr)
  · rintro t ⟨ht, htc, het⟩
    have hv (x : E) (hx : x ∈ t) : x ∈ K.vertices :=
      K.down_closed ht (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)
    let b : Finset K.vertices := t.subtype (fun x => x ∈ K.vertices)
    have hbt : b.map emb = t := Finset.subtype_map_of_mem hv
    have hb : b ∈ A.faces := by
      change b.map emb ∈ K.faces
      rw [hbt]
      exact ht
    have hbc : b.card = 3 := by
      calc
        b.card = (b.map emb).card := by rw [Finset.card_map]
        _ = 3 := by rw [hbt]; exact htc
    have heb : e.val ⊆ b := Finset.map_subset_map.mp (hbt.symm ▸ het)
    refine ⟨⟨b, hb, hbc⟩, ?_, hbt⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heb⟩

end Geometry.SimplicialComplex
