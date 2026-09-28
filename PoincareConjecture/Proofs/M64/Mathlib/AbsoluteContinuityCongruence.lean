import Mathlib.MeasureTheory.Function.AbsolutelyContinuous









set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareConjecture




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

end PoincareConjecture
