import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GraphWalkOriginalEdges
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonBoundaryLoop
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricWalkPaths

set_option autoImplicit false

open Set

namespace Path

private theorem map_finite_concat {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {n : ℕ} (f : C(X, Y)) (a : Fin (n + 1) → X)
    (p : (i : Fin n) → Path (a i.castSucc) (a i.succ)) :
    (concat a p).map f.continuous =
      concat (f ∘ a) (fun i => (p i).map f.continuous) := by
  induction n with
  | zero => rw [concat_zero, concat_zero]; rfl
  | succ n ih =>
    erw [concat_succ, concat_succ, map_trans, ih]
    rfl

private theorem map_concat_of_edge_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {n : ℕ} (f : C(X, Y))
    (a : Fin (n + 1) → X) (b : Fin (n + 1) → Y) (h : ∀ i, f (a i) = b i)
    (p : (i : Fin n) → Path (a i.castSucc) (a i.succ))
    (q : (i : Fin n) → Path (b i.castSucc) (b i.succ))
    (hp : ∀ i, (p i).map f.continuous = (q i).cast (h i.castSucc) (h i.succ)) :
    (concat a p).map f.continuous = (concat b q).cast (h 0) (h (Fin.last n)) := by
  have hb : f ∘ a = b := funext h
  subst b
  have hp' : (fun i => (p i).map f.continuous) = q := funext hp
  rw [map_finite_concat, hp']
  rfl

end Path

namespace SimpleGraph.Walk

private theorem realizePath_homotopic_edges_of_length
    {V X : Type*} [TopologicalSpace X] {G : SimpleGraph V}
    (a : V → X) (edge : ∀ {u v : V}, G.Adj u v → _root_.Path (a u) (a v))
    {u v : V} (w : G.Walk u v) {n : ℕ} (hn : n = w.length) :
    ((realizePath a edge w).cast (congrArg a w.getVert_zero)
      (congrArg a (show w.getVert n = v by rw [hn, w.getVert_length]))).Homotopic
        (_root_.Path.concat (fun i : Fin (n + 1) => a (w.getVert i.val))
          (fun i : Fin n => edge (w.adj_getVert_succ (by
            change i.val < w.length
            exact i.isLt.trans_eq hn)))) := by
  subst n
  exact realizePath_homotopic_original_edges a edge w

end SimpleGraph.Walk

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

theorem polygon_boundaryLoop_homotopic_geometricWalk {v : K.vertices}
    (w : K.vertexAbstractComplex.edgeGraph.Walk v v) {n : ℕ}
    (P : Polygon E (n + 3)) (hlen : n + 3 = w.length)
    (hvertices : ∀ i : Fin (n + 3), P i = (w.getVert i.val : E))
    (hbase : P 0 = (v : E)) (hsub : P.boundary ℝ ⊆ K.space) :
    ((P.boundaryLoop.map (continuous_inclusion hsub)).cast
      (Subtype.ext hbase.symm) (Subtype.ext hbase.symm)).Homotopic
        (K.geometricWalkPath w) := by
  let incl : C(P.boundary ℝ, K.space) := ⟨Set.inclusion hsub, continuous_inclusion hsub⟩
  let a : K.vertices → K.space := fun x => ⟨x, K.vertices_subset_space x.property⟩
  let b : Fin (n + 4) → K.space := fun i => a (w.getVert i.val)
  let q (i : Fin (n + 3)) :=
    K.geometricEdgePath (w.adj_getVert_succ (show i.val < w.length by omega))
  have hpoint (i : Fin (n + 4)) :
      (P.closedBoundaryVertices i : E) = (w.getVert i.val : E) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [P.closedBoundaryVertices_last]
      change P 0 = (w.getVert (n + 3) : E)
      have hlast : w.getVert (n + 3) = v := by rw [hlen, w.getVert_length]
      exact hbase.trans (congrArg Subtype.val hlast).symm
    · rw [P.closedBoundaryVertices_castSucc]
      exact hvertices j
  have hb (i : Fin (n + 4)) : incl (P.closedBoundaryVertices i) = b i :=
    Subtype.ext (hpoint i)
  have hq (i : Fin (n + 3)) :
      (P.closedBoundaryEdgePath i).map incl.continuous =
        (q i).cast (hb i.castSucc) (hb i.succ) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change AffineMap.lineMap (P.closedBoundaryVertices i.castSucc : E)
        (P.closedBoundaryVertices i.succ : E) (t : ℝ) =
      AffineMap.lineMap (w.getVert i.val : E) (w.getVert (i.val + 1) : E) (t : ℝ)
    rw [hpoint, hpoint]
    rfl
  have hconcat := Path.map_concat_of_edge_eq incl P.closedBoundaryVertices b hb
    P.closedBoundaryEdgePath q hq
  have hwalk := SimpleGraph.Walk.realizePath_homotopic_edges_of_length a
    (fun h => K.geometricEdgePath h) w hlen
  have h := hwalk.symm.pathCast (hb 0) (hb (Fin.last (n + 3)))
  erw [← hconcat] at h
  have hstart : a v = incl (P.closedBoundaryVertices 0) := by
    rw [P.closedBoundaryVertices_zero]
    exact Subtype.ext hbase.symm
  have hend : a v = incl (P.closedBoundaryVertices (Fin.last (n + 3))) := by
    rw [P.closedBoundaryVertices_last]
    exact Subtype.ext hbase.symm
  exact h.pathCast hstart hend

end Geometry.SimplicialComplex
