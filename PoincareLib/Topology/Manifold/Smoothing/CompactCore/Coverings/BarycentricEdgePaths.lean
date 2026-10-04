import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Coverings.CocycleFaceSheets
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ComplexCycleLabels
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexSubtypePaths

/-!
# Original barycentric edge paths and their exact sheet transport

The path is the literal straight segment joining the two original vertices.
Its lift changes the endpoint label by precisely the edge-cocycle value.
See Hatcher, Proposition 1.30, and Wall derivation 019.
-/

set_option autoImplicit false

open Set StdSimplexCore

namespace AbstractSimplicialComplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : AbstractSimplicialComplex ι)

noncomputable def barycentricEdgePath {u v : ι} (h : A.edgeGraph.Adj u v) :
    Path (A.toPreAbstractSimplicialComplex.barycentricVertex u (A.singleton_mem u))
      (A.toPreAbstractSimplicialComplex.barycentricVertex v (A.singleton_mem v)) :=
  Path.segmentIn _ _ _ ((convex_barycentricFace {u, v}).segment_subset
    (single_mem_barycentricFace (by simp))
    (single_mem_barycentricFace (by simp)) |>.trans
      (A.toPreAbstractSimplicialComplex.barycentricFace_subset_barycentricSpace h.2))

theorem barycentricEdgePath_mem_face {u v : ι} (h : A.edgeGraph.Adj u v)
    (t : unitInterval) : (A.barycentricEdgePath h t).val ∈ barycentricFace {u, v} :=
  Path.segmentIn_mem_convex (convex_barycentricFace {u, v}) _ _ _
    (single_mem_barycentricFace (by simp)) (single_mem_barycentricFace (by simp)) t

theorem exists_barycentricEdge_lift
    (c : A.toPreAbstractSimplicialComplex.ModTwoEdgeCocycle)
    {u v : ι} (h : A.edgeGraph.Adj u v) (b : ZMod 2) :
    ∃ L : Path
      ((c.bundle.localTriv u).toOpenPartialHomeomorph.symm
        (A.toPreAbstractSimplicialComplex.barycentricVertex u (A.singleton_mem u), b))
      ((c.bundle.localTriv v).toOpenPartialHomeomorph.symm
        (A.toPreAbstractSimplicialComplex.barycentricVertex v (A.singleton_mem v),
          b + c.value u v)),
      ∀ t, c.bundle.proj (L t) = A.barycentricEdgePath h t := by
  exact c.exists_closedFace_lift h.2 (by simp) (by simp) b
    (A.barycentricEdgePath h) (A.barycentricEdgePath_mem_face h)

end AbstractSimplicialComplex
