import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GraphCycleExclusion
import PoincareConjecture.Proofs.M76.Mathlib.VertexAbstractComplex
import PoincareConjecture.Proofs.M76.Mathlib.ComplexCycleLabels
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSubtypePaths

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

noncomputable def geometricEdgePath {u v : K.vertices}
    (h : K.vertexAbstractComplex.edgeGraph.Adj u v) :
    Path (⟨u, K.vertices_subset_space u.property⟩ : K.space)
      ⟨v, K.vertices_subset_space v.property⟩ :=
  Path.segmentIn K.space _ _ (by
    have hface := h.2
    change ({u, v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
      at hface
    have he : ({(u : E), (v : E)} : Finset E) ∈ K.faces := by
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
        using hface
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using
      K.convexHull_subset_space he)

theorem geometricEdgePath_symm {u v : K.vertices}
    (h : K.vertexAbstractComplex.edgeGraph.Adj u v) :
    K.geometricEdgePath h.symm = (K.geometricEdgePath h).symm := by
  ext t
  change Path.segment (v : E) (u : E) t = (Path.segment (u : E) (v : E)).symm t
  exact congrArg (fun p : Path (v : E) (u : E) => p t)
    (Path.segment_symm (u : E) (v : E)).symm

noncomputable def geometricWalkPath {u v : K.vertices}
    (w : K.vertexAbstractComplex.edgeGraph.Walk u v) :
    Path (⟨u, K.vertices_subset_space u.property⟩ : K.space)
      ⟨v, K.vertices_subset_space v.property⟩ :=
  w.realizePath (fun x : K.vertices => (⟨x, K.vertices_subset_space x.property⟩ : K.space))
    (fun h => K.geometricEdgePath h)

theorem exists_excluded_geometric_cycle {b : K.space}
    (J : Subgroup (FundamentalGroup K.space b)) {v : K.vertices}
    (w : K.vertexAbstractComplex.edgeGraph.Walk v v)
    (p : Path b (⟨v, K.vertices_subset_space v.property⟩ : K.space))
    (houtside : p.whiskeredLoopClass (K.geometricWalkPath w) ∉ J) :
    ∃ (u : K.vertices) (c : K.vertexAbstractComplex.edgeGraph.Walk u u)
      (q : Path b (⟨u, K.vertices_subset_space u.property⟩ : K.space)),
      c.IsCycle ∧ q.whiskeredLoopClass (K.geometricWalkPath c) ∉ J := by
  apply SimpleGraph.Walk.exists_excluded_realized_cycle
    (fun x : K.vertices => (⟨x, K.vertices_subset_space x.property⟩ : K.space))
    (fun h => K.geometricEdgePath h) ?_ J w p houtside
  intro u v h
  rw [K.geometricEdgePath_symm h]

end Geometry.SimplicialComplex
