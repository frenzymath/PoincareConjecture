import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegions
import PoincareConjecture.Proofs.M76.Mathlib.PolygonIndexRegions









set_option autoImplicit false

open Set

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (hnv : P.HasNonverticalEdges)

include hP hinj hnv



theorem mem_inside_iff_crossingIndex_ne_zero {q : ℝ × ℝ} (hq : q ∈ (P.boundary ℝ)ᶜ) :
    q ∈ P.inside ↔ P.crossingIndex q ≠ 0 := by
  have hz := P.crossingIndex_eq_zero_iff_unbounded hP hinj hnv hq
  simpa only [inside, mem_ofPred_eq, hq, true_and, not_not] using (not_congr hz).symm



theorem mem_outside_iff_crossingIndex_eq_zero {q : ℝ × ℝ} (hq : q ∈ (P.boundary ℝ)ᶜ) :
    q ∈ P.outside ↔ P.crossingIndex q = 0 := by
  have hz := P.crossingIndex_eq_zero_iff_unbounded hP hinj hnv hq
  simpa only [outside, mem_ofPred_eq, hq, true_and] using hz.symm




theorem crossingIndex_eq_one_or_neg_one_of_mem_inside {q : ℝ × ℝ} (hq : q ∈ P.inside) :
    P.crossingIndex q = 1 ∨ P.crossingIndex q = -1 := by
  have hne := (P.mem_inside_iff_crossingIndex_ne_zero hP hinj hnv hq.1).mp hq
  have hvalues := P.crossingIndex_mem_three hP hinj hnv hq.1
  omega

end Polygon
