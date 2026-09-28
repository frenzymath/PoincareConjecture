import PoincareConjecture.Proofs.M76.Mathlib.ComplexCycleLabels
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]





theorem faceLink_faceLink (K : SimplicialComplex 𝕜 E) (s t : Finset E)
    (hst : Disjoint s t) : (K.faceLink s).faceLink t = K.faceLink (s ∪ t) := by
  ext u
  change ((u ∈ K.faces ∧ Disjoint s u ∧ s ∪ u ∈ K.faces) ∧ Disjoint t u ∧
      (t ∪ u ∈ K.faces ∧ Disjoint s (t ∪ u) ∧ s ∪ (t ∪ u) ∈ K.faces)) ↔
    (u ∈ K.faces ∧ Disjoint (s ∪ t) u ∧ (s ∪ t) ∪ u ∈ K.faces)
  constructor
  · rintro ⟨hu, htu, hstu⟩
    exact ⟨hu.1, Finset.disjoint_union_left.mpr ⟨hu.2.1, htu⟩,
      by simpa only [Finset.union_assoc] using hstu.2.2⟩
  · rintro ⟨hu, hsu, hstu⟩
    obtain ⟨hsu, htu⟩ := Finset.disjoint_union_left.mp hsu
    have hne := K.nonempty_of_mem_faces hu
    refine ⟨⟨hu, hsu, ?_⟩, htu, ?_, Finset.disjoint_union_right.mpr ⟨hst, hsu⟩, ?_⟩
    · exact K.down_closed hstu
        (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl u))
        (Finset.union_nonempty.mpr (Or.inr hne))
    · exact K.down_closed hstu
        (Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl u))
        (Finset.union_nonempty.mpr (Or.inr hne))
    · simpa only [Finset.union_assoc] using hstu




theorem edgeGraph_adj_iff_mem_faceLink (K : SimplicialComplex 𝕜 E) (u v : K.vertices) :
    K.vertexAbstractComplex.edgeGraph.Adj u v ↔ v.val ∈ (K.faceLink {u.val}).vertices := by
  change (u ≠ v ∧ ({u, v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces) ↔
    ({v.val} ∈ K.faces ∧ Disjoint ({u.val} : Finset E) {v.val} ∧
      ({u.val} : Finset E) ∪ {v.val} ∈ K.faces)
  simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype,
    Finset.singleton_union, Finset.disjoint_singleton_left, Finset.mem_singleton]
  constructor
  · rintro ⟨huv, hface⟩
    exact ⟨v.property, fun h => huv (Subtype.ext h), hface⟩
  · rintro ⟨_, huv, hface⟩
    exact ⟨fun h => huv (congrArg Subtype.val h), hface⟩




theorem image_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E) (u : K.vertices) :
    Subtype.val '' K.vertexAbstractComplex.edgeGraph.neighborSet u =
      (K.faceLink {u.val}).vertices := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (K.edgeGraph_adj_iff_mem_faceLink u v).mp hv
  · intro hx
    let v : K.vertices := ⟨x, (K.faceLink_vertices_subset {u.val} hx).1⟩
    exact ⟨v, (K.edgeGraph_adj_iff_mem_faceLink u v).mpr hx, rfl⟩




theorem ncard_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E) (u : K.vertices) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet u).ncard =
      (K.faceLink {u.val}).vertices.ncard := by
  rw [← K.image_edgeGraph_neighborSet u, ncard_image_of_injective _ Subtype.val_injective]




theorem ncard_faceLink_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E)
    (s : Finset E) (u : (K.faceLink s).vertices) :
    ((K.faceLink s).vertexAbstractComplex.edgeGraph.neighborSet u).ncard =
      (K.faceLink (s ∪ {u.val})).vertices.ncard := by
  rw [(K.faceLink s).ncard_edgeGraph_neighborSet u,
    K.faceLink_faceLink s {u.val} u.property.2.1]

end Geometry.SimplicialComplex
