import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Set.Finite.Basic










set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem segment_inter_subset_convexHull_of_isExtreme {a b c d : E}
    (hleft : IsExtreme ℝ (segment ℝ a b) (segment ℝ a b ∩ segment ℝ c d))
    (hright : IsExtreme ℝ (segment ℝ c d) (segment ℝ a b ∩ segment ℝ c d)) :
    segment ℝ a b ∩ segment ℝ c d ⊆
      convexHull ℝ (({a, b} : Set E) ∩ {c, d}) := by
  have hext : (segment ℝ a b ∩ segment ℝ c d).extremePoints ℝ ⊆
      ({a, b} : Set E) ∩ {c, d} := by
    intro x hx
    constructor
    · apply extremePoints_convexHull_subset (𝕜 := ℝ)
      rw [convexHull_pair]
      exact hleft.extremePoints_subset_extremePoints hx
    · apply extremePoints_convexHull_subset (𝕜 := ℝ)
      rw [convexHull_pair]
      exact hright.extremePoints_subset_extremePoints hx
  have hab : IsCompact (segment ℝ a b) := by
    rw [← convexHull_pair]
    exact ((finite_singleton b).insert a).isCompact_convexHull ℝ
  have hcd : IsCompact (segment ℝ c d) := by
    rw [← convexHull_pair]
    exact ((finite_singleton d).insert c).isCompact_convexHull ℝ
  have hcomp : IsCompact (segment ℝ a b ∩ segment ℝ c d) := hab.inter_right hcd.isClosed
  have hconv := (convex_segment (𝕜 := ℝ) a b).inter (convex_segment c d)
  have hclosed := (((finite_singleton b).insert a).inter_of_left {c, d}).isClosed_convexHull ℝ
  calc
    segment ℝ a b ∩ segment ℝ c d =
        closure (convexHull ℝ ((segment ℝ a b ∩ segment ℝ c d).extremePoints ℝ)) :=
      (closure_convexHull_extremePoints hcomp hconv).symm
    _ ⊆ closure (convexHull ℝ (({a, b} : Set E) ∩ {c, d})) :=
      closure_mono (convexHull_mono hext)
    _ = _ := hclosed.closure_eq
