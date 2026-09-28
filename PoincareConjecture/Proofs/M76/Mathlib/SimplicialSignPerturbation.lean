import PoincareConjecture.Proofs.M76.Mathlib.ConnectedHalfspaceGraph
import PoincareConjecture.Proofs.M76.Mathlib.GraphAttachedVertices
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBirthStar











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]





theorem exists_positive_graph_neighbor_of_mem_closure
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : E →ᵃ[ℝ] ℝ) (q : K.vertices) (hq : A q = 0)
    (hacc : (q : E) ∈ closure (K.space ∩ {x | 0 < A x})) :
    ∃ v : K.vertices, K.vertexAbstractComplex.edgeGraph.Adj q v ∧ 0 < A v := by
  obtain ⟨ε, hε, hnear⟩ := K.exists_ball_inter_space_subset_closedStar hK q.property
  obtain ⟨x, hxball, hxK, hxA⟩ := mem_closure_iff.mp hacc (Metric.ball q ε)
    Metric.isOpen_ball (Metric.mem_ball_self hε)
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp (hnear ⟨hxK, hxball⟩)
  have hpositive : ∃ v ∈ s, 0 < A v := by
    by_contra h
    push_neg at h
    have hbound : convexHull ℝ (s : Set E) ⊆ {y | A y ≤ 0} :=
      convexHull_min (fun y hy => h y hy) ((convex_Iic (0 : ℝ)).affine_preimage A)
    exact (show 0 < A x from hxA).not_ge (hbound hxs)
  obtain ⟨v, hv, hvA⟩ := hpositive
  have hvK : v ∈ K.vertices := K.down_closed hs.1
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hqv : (q : E) ≠ v := by
    intro h
    exact hvA.ne' (h ▸ hq)
  refine ⟨⟨v, hvK⟩, ⟨fun h => hqv (congrArg Subtype.val h), ?_⟩, hvA⟩
  change ({q, (⟨v, hvK⟩ : K.vertices)} : Finset K.vertices).map
    (Function.Embedding.subtype _) ∈ K.faces
  simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
  apply K.down_closed hs.2 ?_ (Finset.insert_nonempty _ _)
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((Finset.mem_singleton.mp hy).symm ▸ hv)

variable [FiniteDimensional ℝ E]





theorem preconnected_positive_vertex_graph_of_sign_preservation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : E →ᵃ[ℝ] ℝ) (f : E → ℝ)
    (hconn : IsPreconnected (K.space ∩ {x | 0 < A x}))
    (hpos : ∀ v ∈ K.vertices, 0 < A v → 0 < f v)
    (hneg : ∀ v ∈ K.vertices, A v < 0 → f v < 0)
    (hzero : ∀ v ∈ K.vertices, A v = 0 →
      v ∈ closure (K.space ∩ {x | 0 < A x})) :
    (K.vertexAbstractComplex.edgeGraph.induce
      {v : K.vertices | 0 < f (v : E)}).Preconnected := by
  have hgraph := K.preconnected_positive_vertex_graph_of_isPreconnected hK A hconn
  apply hgraph.induce_of_attached_vertices
  · exact fun v hv => hpos v v.property hv
  · intro q hqf hqnot
    have hqA : A q = 0 := le_antisymm (le_of_not_gt hqnot) (le_of_not_gt (fun h =>
      (hneg q q.property h).not_ge (show 0 ≤ f q from hqf.le)))
    obtain ⟨v, hqv, hvA⟩ := K.exists_positive_graph_neighbor_of_mem_closure hK A q hqA
      (hzero q q.property hqA)
    exact ⟨v, hvA, hqv⟩

end Geometry.SimplicialComplex
