import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricWalkPaths
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

theorem exists_polygon_of_geometric_cycle {v : K.vertices}
    (w : K.vertexAbstractComplex.edgeGraph.Walk v v) (hw : w.IsCycle) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), n + 3 = w.length ∧
      (∀ i : Fin (n + 3), P i = (w.getVert i.val : E)) ∧
      P 0 = (v : E) ∧ Function.Injective P ∧ P.HasSimplicialEdges ∧
      (∀ i, P.edgeVertices i ∈ K.faces) ∧ P.boundary ℝ ⊆ K.space := by
  let n := w.length - 3
  have hlength : n + 3 = w.length := Nat.sub_add_cancel hw.three_le_length
  let P : Polygon E (n + 3) := ⟨fun i => (w.getVert i.val : E)⟩
  have hnext (i : Fin (n + 3)) : w.getVert (i + 1).val = w.getVert (i.val + 1) := by
    by_cases hi : i.val + 1 < n + 3
    · rw [Fin.val_add_one_of_lt' hi]
    · have he : i.val + 1 = w.length := by omega
      have hzero : i + 1 = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one, Fin.val_zero]
        rw [he, ← hlength, Nat.mod_self]
      rw [hzero, he, SimpleGraph.Walk.getVert_length]
      exact w.getVert_zero
  have hinj : Function.Injective P := by
    intro i j hij
    apply Fin.ext
    apply hw.getVert_injOn' (by change i.val ≤ w.length - 1; omega)
      (by change j.val ≤ w.length - 1; omega)
    exact Subtype.ext hij
  have hface (i : Fin (n + 3)) : P.edgeVertices i ∈ K.faces := by
    have hadj := w.adj_getVert_succ (show i.val < w.length by omega)
    have h := hadj.2
    change ({w.getVert i.val, w.getVert (i.val + 1)} : Finset K.vertices).map
      (Function.Embedding.subtype _) ∈ K.faces at h
    have heq : P.edgeVertices i =
        ({(w.getVert i.val : E), (w.getVert (i.val + 1) : E)} : Finset E) := by
      ext x
      simp only [Polygon.edgeVertices, P, finRotate_apply, hnext,
        Finset.mem_insert, Finset.mem_singleton]
    rw [heq]
    simpa only [Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] using h
  have hP : P.HasSimplicialEdges := by
    intro i j
    rw [P.edgeSet_eq_convexHull, P.edgeSet_eq_convexHull]
    exact K.inter_subset_convexHull (hface i) (hface j)
  refine ⟨n, P, hlength, fun _ => rfl, ?_, hinj, hP, hface, ?_⟩
  · exact congrArg Subtype.val w.getVert_zero
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [P.edgeSet_eq_convexHull] at hi
    exact K.convexHull_subset_space (hface i) hi

end Geometry.SimplicialComplex
