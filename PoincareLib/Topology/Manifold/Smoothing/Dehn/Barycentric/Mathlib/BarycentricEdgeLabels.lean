import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricFullSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ConnectedComplexGraph

/-!
# Exact original face labels for the centroid edge graph

Every derived vertex retains its unique original nonempty face. Its graph
edges are precisely the distinct comparable face labels. These literal
labels identify the two colored graphs with the subdivisions of the original
primal and complementary trees. See Hudson pp. 8--9, Putman, Theorem 5.1,
pp. 15--16, and M76 Dehn derivation 021, section 1.
-/

set_option autoImplicit false

namespace PreAbstractSimplicialComplex

variable {V : Type*}

/-- Distinct comparable original nonempty faces form the edges of the
face-inclusion graph. See Dehn derivation 021, section 1. -/
def faceInclusionGraph (A : PreAbstractSimplicialComplex V) : SimpleGraph A.faces where
  Adj s t := s ≠ t ∧ (s.val ⊆ t.val ∨ t.val ⊆ s.val)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end PreAbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

/-- The actual centroid map bijects original faces with the vertices of
the same barycentric subdivision. See Dehn derivation 021, section 1. -/
noncomputable def faceCentroidVertexEquiv : K.faces ≃ K.barycentricSubdivision.vertices :=
  Equiv.ofBijective
    (fun s => ⟨s.val.centroid ℝ id,
      (K.mem_barycentricSubdivision_vertices_iff _).mpr ⟨s.val, s.property, rfl⟩⟩)
    ⟨fun _ _ h => K.faceCentroid_injective (congrArg Subtype.val h), by
      intro p
      obtain ⟨s, hs, hsp⟩ := (K.mem_barycentricSubdivision_vertices_iff p.val).mp p.property
      exact ⟨⟨s, hs⟩, Subtype.ext hsp⟩⟩

/-- The vertex label equivalence uses the literal original face centroid.
See Dehn derivation 021, section 1. -/
theorem faceCentroidVertexEquiv_apply_val (s : K.faces) :
    (K.faceCentroidVertexEquiv s).val = s.val.centroid ℝ id := rfl

variable [DecidableEq E]

/-- Two actual original face centroids span a derived face exactly when
their whole original faces are comparable. See Hudson pp. 8--9 and Dehn 021. -/
theorem barycentric_centroid_pair_face_iff (s t : K.faces) :
    ({s.val.centroid ℝ id, t.val.centroid ℝ id} : Finset E) ∈
        K.barycentricSubdivision.faces ↔ s.val ⊆ t.val ∨ t.val ⊆ s.val := by
  classical
  constructor
  · intro h
    obtain ⟨a, _, hchain, hfa⟩ := (K.barycentricSubdivision_faces _).mp h
    have hs : s ∈ a := by
      obtain ⟨u, hu, hus⟩ := Finset.mem_image.mp
        (hfa ▸ Finset.mem_insert_self (s.val.centroid ℝ id) {t.val.centroid ℝ id})
      have he : u = s := K.faceCentroid_injective hus
      exact he ▸ hu
    have ht : t ∈ a := by
      obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp
        (hfa ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self (t.val.centroid ℝ id)))
      have he : u = t := K.faceCentroid_injective hut
      exact he ▸ hu
    exact hchain s hs t ht
  · intro h
    apply (K.barycentricSubdivision_faces _).mpr
    refine ⟨{s, t}, Finset.insert_nonempty s {t}, ?_, ?_⟩
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact Or.inl le_rfl
      · exact h
      · exact h.elim Or.inr Or.inl
      · exact Or.inl le_rfl
    · simp only [Finset.image_insert, Finset.image_singleton]

/-- The entire actual centroid edge graph is the original face-inclusion
graph under the literal centroid vertex equivalence. Both adjacency
directions retain the full original labels. See Dehn 021, section 1. -/
noncomputable def faceCentroidGraphIso :
    K.toPreAbstractSimplicialComplex.faceInclusionGraph ≃g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph where
  toEquiv := K.faceCentroidVertexEquiv
  map_rel_iff' := by
    intro s t
    constructor
    · intro h
      refine ⟨fun he => h.1 (congrArg K.faceCentroidVertexEquiv he), ?_⟩
      have hface := h.2
      change ({K.faceCentroidVertexEquiv s, K.faceCentroidVertexEquiv t} :
        Finset K.barycentricSubdivision.vertices).map (Function.Embedding.subtype _) ∈
          K.barycentricSubdivision.faces at hface
      have hpair : ({s.val.centroid ℝ id, t.val.centroid ℝ id} : Finset E) ∈
          K.barycentricSubdivision.faces := by
        simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype,
          K.faceCentroidVertexEquiv_apply_val] using hface
      exact (K.barycentric_centroid_pair_face_iff s t).mp hpair
    · intro h
      refine ⟨fun he => h.1 (K.faceCentroidVertexEquiv.injective he), ?_⟩
      change ({K.faceCentroidVertexEquiv s, K.faceCentroidVertexEquiv t} :
        Finset K.barycentricSubdivision.vertices).map (Function.Embedding.subtype _) ∈
          K.barycentricSubdivision.faces
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype,
        K.faceCentroidVertexEquiv_apply_val] using
        (K.barycentric_centroid_pair_face_iff s t).mpr h.2

end Geometry.SimplicialComplex
