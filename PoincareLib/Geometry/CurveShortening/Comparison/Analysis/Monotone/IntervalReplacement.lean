import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Monotone replacement on a real interval

Replacing a continuous monotone function by another monotone function
with matching endpoint values preserves continuity and monotonicity.
This is the elementary boundary-label step in M64's derivation
`2026-09-26-free-boundary-replacement.md` (Lemaire 1982, p. 102).

Morgan--Tian context: Lemma 19.15, printed pp. 447-449. This project analytic helper
supports the actual annular minimizer and boundary regularity construction.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set

namespace PoincareMT

/-- Matching endpoint values allow continuous monotone interpolation on a closed interval,
including collapsed image intervals. Source: M64 free-boundary-replacement derivation, label
construction. Source/construction:
proof-work/tasks/M64/derivations/2026-09-26-free-boundary-replacement.md, Producing the
changed labels. -/
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

end PoincareMT
