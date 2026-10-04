import PoincareLib.Topology.Manifold.Smoothing.Dehn.Graphs.Mathlib.GraphCycleExclusion
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.VertexAbstractComplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ComplexCycleLabels
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexSubtypePaths

/-!
# The original geometric graph supplies its own edge paths

Each actual two-vertex face gives its literal straight segment in
the unchanged complex carrier. Reverse edges reverse those paths.
Thus the based cycle selection uses paths entirely inside the
original finite rim image. See Stallings, section 2.A.2, p. 11,
and Dehn derivation 024, sections 2--3.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

/-- The actual directed edge is its whole straight segment in the
original complex carrier. See Dehn 024, section 2. -/
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

/-- Reversing the original geometric edge reverses its actual
subtype-valued path pointwise. See Dehn 024, section 2. -/
theorem geometricEdgePath_symm {u v : K.vertices}
    (h : K.vertexAbstractComplex.edgeGraph.Adj u v) :
    K.geometricEdgePath h.symm = (K.geometricEdgePath h).symm := by
  ext t
  change Path.segment (v : E) (u : E) t = (Path.segment (u : E) (v : E)).symm t
  exact congrArg (fun p : Path (v : E) (u : E) => p t)
    (Path.segment_symm (u : E) (v : E)).symm

/-- Realize a walk using precisely the original straight edges.
The whole path takes values in the unchanged geometric carrier.
See Stallings p. 11 and Dehn 024, section 2. -/
noncomputable def geometricWalkPath {u v : K.vertices}
    (w : K.vertexAbstractComplex.edgeGraph.Walk u v) :
    Path (⟨u, K.vertices_subset_space u.property⟩ : K.space)
      ⟨v, K.vertices_subset_space v.property⟩ :=
  w.realizePath (fun x : K.vertices => (⟨x, K.vertices_subset_space x.property⟩ : K.space))
    (fun h => K.geometricEdgePath h)

/-- An excluded original geometric walk yields a simple cycle
and a retained actual whisker inside the same carrier. All edge
path data are constructed from original faces here.
See Stallings p. 11 and Dehn 024, section 3. -/
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
