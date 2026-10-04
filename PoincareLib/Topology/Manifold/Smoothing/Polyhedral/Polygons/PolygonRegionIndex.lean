import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonIndexRegions

/-!
# Crossing-index tests for the canonical polygon regions

The canonical bounded and unbounded regions are detected by
nonzero and zero signed ray count. See Erickson, Simple Polygons,
pp. 4--8 and M76 derivations 101--102.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (hnv : P.HasNonverticalEdges)

include hP hinj hnv

/-- Off the boundary, a query is inside precisely when its
signed ray count is nonzero. See Erickson pp. 4--6 and derivation 101. -/
theorem mem_inside_iff_crossingIndex_ne_zero {q : ℝ × ℝ} (hq : q ∈ (P.boundary ℝ)ᶜ) :
    q ∈ P.inside ↔ P.crossingIndex q ≠ 0 := by
  have hz := P.crossingIndex_eq_zero_iff_unbounded hP hinj hnv hq
  simpa only [inside, mem_ofPred_eq, hq, true_and, not_not] using (not_congr hz).symm

/-- Off the boundary, a query is outside precisely when its
signed ray count is zero. See Erickson pp. 4--6 and derivation 101. -/
theorem mem_outside_iff_crossingIndex_eq_zero {q : ℝ × ℝ} (hq : q ∈ (P.boundary ℝ)ᶜ) :
    q ∈ P.outside ↔ P.crossingIndex q = 0 := by
  have hz := P.crossingIndex_eq_zero_iff_unbounded hP hinj hnv hq
  simpa only [outside, mem_ofPred_eq, hq, true_and] using hz.symm

/-- Inside a simple polygon the index is +1 or -1, with the
sign depending on its orientation. See Erickson pp. 4--8 and
M76 derivation 101. -/
theorem crossingIndex_eq_one_or_neg_one_of_mem_inside {q : ℝ × ℝ} (hq : q ∈ P.inside) :
    P.crossingIndex q = 1 ∨ P.crossingIndex q = -1 := by
  have hne := (P.mem_inside_iff_crossingIndex_ne_zero hP hinj hnv hq.1).mp hq
  have hvalues := P.crossingIndex_mem_three hP hinj hnv hq.1
  omega

end Polygon
