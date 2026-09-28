import PoincareConjecture.Proofs.M76.Mathlib.PureEdgeComplexPolygon
import PoincareConjecture.Proofs.M76.Mathlib.GeometricPathIntervals









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]




theorem actual_edgeGraph_segment_intersection (J : SimplicialComplex ℝ E)
    {v w a b : J.vertices}
    (hvw : J.vertexAbstractComplex.edgeGraph.Adj v w)
    (hab : J.vertexAbstractComplex.edgeGraph.Adj a b) :
    segment ℝ (v : E) (w : E) ∩ segment ℝ (a : E) (b : E) ⊆
      convexHull ℝ (({(v : E), (w : E)} : Set E) ∩ {(a : E), (b : E)}) := by
  have hedge {x y : J.vertices} (h : J.vertexAbstractComplex.edgeGraph.Adj x y) :
      ({(x : E), (y : E)} : Finset E) ∈ J.faces := by
    have hxy := h.2
    change ({x, y} : Finset J.vertices).map (Function.Embedding.subtype _) ∈ J.faces at hxy
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
      using hxy
  simpa only [Finset.coe_pair, convexHull_pair] using
    J.inter_subset_convexHull (hedge hvw) (hedge hab)




theorem actual_edgeGraph_segmentCarrier_eq_space (J : SimplicialComplex ℝ E)
    (hdim : ∀ s ∈ J.faces, s.card ≤ 2)
    (hne : ∀ v : J.vertices, (J.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty) :
    J.vertexAbstractComplex.edgeGraph.segmentCarrier ((↑) : J.vertices → E) = J.space := by
  classical
  let G := J.vertexAbstractComplex.edgeGraph
  have hedge {v w : J.vertices} (h : G.Adj v w) :
      ({(v : E), (w : E)} : Finset E) ∈ J.faces := by
    have h' := h.2
    change ({v, w} : Finset J.vertices).map (Function.Embedding.subtype _) ∈ J.faces at h'
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
      using h'
  have hvertex (v : J.vertices) : (v : E) ∈ G.segmentCarrier ((↑) : J.vertices → E) := by
    obtain ⟨w, hw⟩ := hne v
    exact ⟨v, w, hw, left_mem_segment ℝ _ _⟩
  apply Subset.antisymm
  · rintro x ⟨v, w, hvw, hx⟩
    apply J.convexHull_subset_space (hedge hvw)
    simpa only [Finset.coe_pair, convexHull_pair] using hx
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    have hpos := Finset.card_pos.mpr (J.nonempty_of_mem_faces hs)
    have hcard := hdim s hs
    by_cases hone : s.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      have hxv : x = v := by simpa only [Finset.coe_singleton, convexHull_singleton,
        mem_singleton_iff] using hxs
      subst x
      exact hvertex ⟨v, hs⟩
    · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
      have hv : v ∈ J.vertices := J.face_subset_vertices hs (Finset.mem_insert_self _ _)
      have hw : w ∈ J.vertices := J.face_subset_vertices hs
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hadj : G.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
        refine ⟨fun h => hvw (congrArg Subtype.val h), ?_⟩
        change ({(⟨v, hv⟩ : J.vertices), ⟨w, hw⟩} : Finset J.vertices).map
          (Function.Embedding.subtype _) ∈ J.faces
        simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
          using hs
      exact ⟨⟨v, hv⟩, ⟨w, hw⟩, hadj, by
        simpa only [Finset.coe_pair, convexHull_pair] using hxs⟩

end Geometry.SimplicialComplex
