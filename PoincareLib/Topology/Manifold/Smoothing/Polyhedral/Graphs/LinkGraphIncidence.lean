import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ComplexCycleLabels
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FaceLinkProjection

/-!
# Edge degrees as vertex counts of actual links

Iterated links along disjoint faces equal the link of their union.
The neighbors of an actual vertex are exactly its singleton-link
vertices. This supplies the incidence condition for cyclic normal
links in Cairns 1940, pp. 800, 802, 807; see M76 derivation 41.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

/-- Taking successive links along disjoint finite vertex sets
equals taking the link of their union. Downward closure supplies
all intermediate cofaces.
See Cairns pp. 800, 807 and M76 derivation 41. -/
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

/-- Two actual vertices are adjacent exactly when the second is
a vertex of the first vertex's link.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

/-- Forgetting actual-vertex subtype labels maps the entire
neighbor set onto the singleton-link vertex set.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

/-- The neighbor count is the number of actual singleton-link
vertices, with the same convention for infinite sets on both sides.
See Cairns pp. 802, 807 and M76 derivation 41. -/
theorem ncard_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E) (u : K.vertices) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet u).ncard =
      (K.faceLink {u.val}).vertices.ncard := by
  rw [← K.image_edgeGraph_neighborSet u, ncard_image_of_injective _ Subtype.val_injective]

/-- Degree at a vertex of a face link equals the vertex count
of the enlarged-face link in the original complex.
See Cairns pp. 800, 807 and M76 derivation 41. -/
theorem ncard_faceLink_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E)
    (s : Finset E) (u : (K.faceLink s).vertices) :
    ((K.faceLink s).vertexAbstractComplex.edgeGraph.neighborSet u).ncard =
      (K.faceLink (s ∪ {u.val})).vertices.ncard := by
  rw [(K.faceLink s).ncard_edgeGraph_neighborSet u,
    K.faceLink_faceLink s {u.val} u.property.2.1]

end Geometry.SimplicialComplex
