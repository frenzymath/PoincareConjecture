import PoincareConjecture.Proofs.M76.Mathlib.PolygonPathCycles

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {m n : ℕ}

theorem hasSimplicialEdges_ofPaths_of_intersections
    (u : Fin (m + 2) → E) (v : Fin (n + 2) → E)
    (huv : u (Fin.last (m + 1)) = v 0)
    (hvu : v (Fin.last (n + 1)) = u 0)
    (hu : ∀ i j : Fin (m + 1),
      segment ℝ (u i.castSucc) (u i.succ) ∩ segment ℝ (u j.castSucc) (u j.succ) ⊆
        convexHull ℝ (({u i.castSucc, u i.succ} : Set E) ∩ {u j.castSucc, u j.succ}))
    (hv : ∀ i j : Fin (n + 1),
      segment ℝ (v i.castSucc) (v i.succ) ∩ segment ℝ (v j.castSucc) (v j.succ) ⊆
        convexHull ℝ (({v i.castSucc, v i.succ} : Set E) ∩ {v j.castSucc, v j.succ}))
    (hmix : ∀ (i : Fin (m + 1)) (j : Fin (n + 1)),
      segment ℝ (u i.castSucc) (u i.succ) ∩ segment ℝ (v j.castSucc) (v j.succ) ⊆
        convexHull ℝ (({u i.castSucc, u i.succ} : Set E) ∩ {v j.castSucc, v j.succ})) :
    (ofPaths u v).HasSimplicialEdges := by
  classical
  intro i j
  rw [edgeSet_eq_convexHull, edgeSet_eq_convexHull]
  induction i using Fin.addCases with
  | left i =>
    rw [edgeVertices_ofPaths_left u v huv]
    induction j using Fin.addCases with
    | left j =>
      simpa only [edgeVertices_ofPaths_left u v huv, Finset.coe_pair, convexHull_pair]
        using hu i j
    | right j =>
      simpa only [edgeVertices_ofPaths_right u v hvu, Finset.coe_pair, convexHull_pair]
        using hmix i j
  | right i =>
    rw [edgeVertices_ofPaths_right u v hvu]
    induction j using Fin.addCases with
    | left j =>
      simpa only [edgeVertices_ofPaths_left u v huv, Finset.coe_pair, convexHull_pair,
        inter_comm] using hmix j i
    | right j =>
      simpa only [edgeVertices_ofPaths_right u v hvu, Finset.coe_pair, convexHull_pair]
        using hv i j

end Polygon
