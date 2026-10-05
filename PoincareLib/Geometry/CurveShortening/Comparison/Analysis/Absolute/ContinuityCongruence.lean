import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! Pointwise interval equality preserves absolute continuity. This is
used when lifting the observed semicircle through a closed embedding.
Source: the defining disjoint-interval estimate.

Morgan--Tian context: Lemma 19.15, printed pp. 447-449. This project analytic helper
supports the actual annular minimizer and boundary regularity construction.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareMT

/-- Absolute continuity depends only on the values on the specified closed interval. Source:
derivations/2026-09-26-boundary-semicircle-assembly.md, vector primitive and
closed-embedding lift. -/
theorem m64AbsolutelyContinuousOnInterval_congr
    {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (heq : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := hf epsilon hepsilon
  refine ⟨delta, hdelta, fun E hE hlen => ?_⟩
  have hsum : (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [heq (hE.1 i hi).1, heq (hE.1 i hi).2]
  rw [← hsum]
  exact hbound E hE hlen

end PoincareMT
