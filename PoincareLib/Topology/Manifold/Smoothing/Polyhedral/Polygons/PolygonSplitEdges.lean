import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CyclicEdgeSums
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplicialPolygon

/-!
# Edges of the two polygons obtained by adding a diagonal

The two forward edge strings are the original edges, and each
new closing edge is the diagonal. These identities do not require
simplicity. See Erickson, Simple Polygons, pp. 8--9 and M76
derivation 104.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} {m n : ℕ}

/-- The first split cycle inherits the endpoints of each edge
in the first original string. See M76 derivation 104. -/
theorem edgeVertices_split_left (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (m + 1)) :
    (mk (Fin.snoc u (v 0))).edgeVertices i.castSucc =
      (mk (Fin.append u v)).edgeVertices (i.castAdd (n + 1)) := by
  classical
  have hrot : finRotate ((m + 1) + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  simp only [edgeVertices, hrot, Fin.snoc_castSucc,
    Fin.append_left, Fin.append_finRotate_castAdd]

/-- The second split cycle inherits the endpoints of each edge
in the second original string. See M76 derivation 104. -/
theorem edgeVertices_split_right (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (n + 1)) :
    (mk (Fin.snoc v (u 0))).edgeVertices i.castSucc =
      (mk (Fin.append u v)).edgeVertices (Fin.natAdd (m + 1) i) := by
  classical
  have hrot : finRotate ((n + 1) + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  simp only [edgeVertices, hrot, Fin.snoc_castSucc,
    Fin.append_right, Fin.append_finRotate_natAdd]

/-- Appending a vertex creates the closing edge from that vertex
to the first vertex of the string. See M76 derivation 104. -/
theorem edgeVertices_snoc_last (u : Fin (m + 1) → E) (z : E) :
    ((mk (Fin.snoc u z)).edgeVertices (Fin.last (m + 1)) : Set E) = {z, u 0} := by
  classical
  simp [edgeVertices]

variable [AddCommGroup E] [Module ℝ E]

/-- The first split cycle retains each original edge in its first
string as an actual geometric segment. See M76 derivation 104. -/
theorem edgeSet_split_left (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (m + 1)) :
    (mk (Fin.snoc u (v 0))).edgeSet ℝ i.castSucc =
      (mk (Fin.append u v)).edgeSet ℝ (i.castAdd (n + 1)) := by
  rw [edgeSet_eq_convexHull, edgeSet_eq_convexHull, edgeVertices_split_left]

/-- The second split cycle retains each original edge in its
second string. See M76 derivation 104. -/
theorem edgeSet_split_right (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (n + 1)) :
    (mk (Fin.snoc v (u 0))).edgeSet ℝ i.castSucc =
      (mk (Fin.append u v)).edgeSet ℝ (Fin.natAdd (m + 1) i) := by
  rw [edgeSet_eq_convexHull, edgeSet_eq_convexHull, edgeVertices_split_right]

/-- The new closing edge is precisely the segment between the
last and first vertices. See M76 derivation 104. -/
theorem edgeSet_snoc_last (u : Fin (m + 1) → E) (z : E) :
    (mk (Fin.snoc u z)).edgeSet ℝ (Fin.last (m + 1)) = segment ℝ z (u 0) := by
  rw [edgeSet_eq_convexHull, edgeVertices_snoc_last, convexHull_pair]

/-- The first split boundary consists of its original edge string
and the diagonal. See Erickson pp. 8--9 and M76 derivation 104. -/
theorem boundary_split_left (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) :
    (mk (Fin.snoc u (v 0))).boundary ℝ =
      (⋃ i : Fin (m + 1), (mk (Fin.append u v)).edgeSet ℝ (i.castAdd (n + 1))) ∪
        segment ℝ (u 0) (v 0) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    induction i using Fin.lastCases with
    | last =>
      right
      rwa [edgeSet_snoc_last, segment_symm] at hi
    | cast i =>
      left
      exact mem_iUnion.mpr ⟨i, (edgeSet_split_left u v i) ▸ hi⟩
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.castSucc, (edgeSet_split_left u v i).symm ▸ hi⟩
    · apply mem_iUnion.mpr
      refine ⟨Fin.last (m + 1), ?_⟩
      rwa [edgeSet_snoc_last, segment_symm]

/-- The second split boundary consists of its original edge string
and the same diagonal. See Erickson pp. 8--9 and M76 derivation 104. -/
theorem boundary_split_right (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) :
    (mk (Fin.snoc v (u 0))).boundary ℝ =
      (⋃ i : Fin (n + 1), (mk (Fin.append u v)).edgeSet ℝ (Fin.natAdd (m + 1) i)) ∪
        segment ℝ (u 0) (v 0) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    induction i using Fin.lastCases with
    | last =>
      right
      rwa [edgeSet_snoc_last] at hi
    | cast i =>
      left
      exact mem_iUnion.mpr ⟨i, (edgeSet_split_right u v i) ▸ hi⟩
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.castSucc, (edgeSet_split_right u v i).symm ▸ hi⟩
    · apply mem_iUnion.mpr
      refine ⟨Fin.last (n + 1), ?_⟩
      rwa [edgeSet_snoc_last]

/-- The split boundaries together cover exactly the original boundary
and the added diagonal. See Erickson pp. 8--9 and M76 derivation 104. -/
theorem boundary_split_union (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) :
    (mk (Fin.snoc u (v 0))).boundary ℝ ∪ (mk (Fin.snoc v (u 0))).boundary ℝ =
      (mk (Fin.append u v)).boundary ℝ ∪ segment ℝ (u 0) (v 0) := by
  rw [boundary_split_left, boundary_split_right]
  have h :
      (⋃ i : Fin (m + 1), (mk (Fin.append u v)).edgeSet ℝ (i.castAdd (n + 1))) ∪
        (⋃ i : Fin (n + 1), (mk (Fin.append u v)).edgeSet ℝ (Fin.natAdd (m + 1) i)) =
      (mk (Fin.append u v)).boundary ℝ := by
    ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.castAdd (n + 1), hi⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨Fin.natAdd (m + 1) i, hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      induction i using Fin.addCases with
      | left i => exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
      | right i => exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
  rw [union_union_union_comm, union_self, h]

end Polygon
