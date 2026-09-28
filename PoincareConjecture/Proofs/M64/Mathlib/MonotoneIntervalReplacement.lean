import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set

namespace PoincareConjecture

theorem m64Monotone_interval_replacement
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hg : Continuous g) (hmf : Monotone f) (hmg : Monotone g)
    (ha : g a = f a) (hb : g b = f b) [DecidablePred (· ∈ Icc a b)] :
    Continuous ((Icc a b).piecewise g f) ∧ Monotone ((Icc a b).piecewise g f) := by
  constructor
  · apply hg.piecewise _ hf
    intro x hx
    rw [frontier_Icc hab] at hx
    rcases hx with (rfl | rfl) <;> assumption
  · intro x y hxy
    by_cases hx : x ∈ Icc a b
    · rw [piecewise_eq_of_mem _ _ _ hx]
      by_cases hy : y ∈ Icc a b
      · rw [piecewise_eq_of_mem _ _ _ hy]
        exact hmg hxy
      · rw [piecewise_eq_of_notMem _ _ _ hy]
        have hby : b ≤ y := by
          by_contra h
          exact hy ⟨hx.1.trans hxy, (lt_of_not_ge h).le⟩
        exact (hmg hx.2).trans (hb ▸ hmf hby)
    · rw [piecewise_eq_of_notMem _ _ _ hx]
      by_cases hy : y ∈ Icc a b
      · rw [piecewise_eq_of_mem _ _ _ hy]
        have hxa : x ≤ a := by
          by_contra h
          exact hx ⟨(lt_of_not_ge h).le, hxy.trans hy.2⟩
        exact (hmf hxa).trans (ha ▸ hmg hy.1)
      · rw [piecewise_eq_of_notMem _ _ _ hy]
        exact hmf hxy

end PoincareConjecture
