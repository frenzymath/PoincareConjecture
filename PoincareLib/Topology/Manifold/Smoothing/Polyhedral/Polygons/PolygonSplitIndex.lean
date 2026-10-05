import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CyclicEdgeSums
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.DoubleCurve.PolygonCrossingIndex

/-!
# Exact crossing-index addition for split vertex strings

Reversing an edge negates its signed ray contribution. The two
added diagonal edges therefore cancel for every query. See
Erickson, Simple Polygons, pp. 8--9 and M76 derivation 103.
-/

set_option autoImplicit false

namespace PlanarSegment

/-- Reversing a nonvertical line does not change its height
graph, including outside the segment. See M76 derivation 103. -/
theorem height_swap {a b : ℝ × ℝ} (hab : a.1 ≠ b.1) (x : ℝ) :
    height b a x = height a b x := by
  simp only [height, AffineMap.lineMap_apply_module', smul_eq_mul]
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hab.symm]
  ring

/-- Reversing an edge negates its crossing contribution for every
query. Vertical edges have zero contribution in both directions.
See Erickson pp. 8--9 and M76 derivation 103. -/
theorem crossingContribution_swap (a b q : ℝ × ℝ) :
    crossingContribution b a q = -crossingContribution a b q := by
  by_cases hab : a.1 = b.1
  · simp [crossingContribution, hab]
  · unfold crossingContribution aboveLine
    rw [height_swap hab]
    ring

end PlanarSegment

/-- The two cyclic strings obtained by adding opposite copies of
a diagonal have crossing indices summing to the original index.
This algebraic identity does not require simplicity or nonvertical
edges. See Erickson pp. 8--9 and M76 derivation 103. -/
theorem Polygon.crossingIndex_append_split {m n : ℕ}
    (u : Fin (m + 1) → ℝ × ℝ) (v : Fin (n + 1) → ℝ × ℝ) (q : ℝ × ℝ) :
    (Polygon.mk (Fin.append u v)).crossingIndex q =
      (Polygon.mk (Fin.snoc u (v 0))).crossingIndex q +
        (Polygon.mk (Fin.snoc v (u 0))).crossingIndex q := by
  apply Fin.cyclicEdgeSum_append_split (fun a b => PlanarSegment.crossingContribution a b q)
  rw [PlanarSegment.crossingContribution_swap (u 0) (v 0), add_neg_cancel]
