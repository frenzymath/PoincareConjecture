import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# A competing branch shortens a long minimizing prefix

If a curve of length `a` and another curve of length at most `b < a`
join the same endpoints, the first curve stops minimizing no later than
`(a + b) / 2`. The proof uses the shortcut through the common endpoint.

This is the metric step in Maeder--Baumdicker--Seidel, Corollary 4.12, p. 31.
-/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace Poincare

/-- A shortcut of length `b` to the terminal point bounds the length of any
minimizing prefix of a curve of length `a > b`. -/
theorem minimizing_prefix_le_average_of_shortcut
    {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {p q : X}
    {a b r : ℝ} (hb : 0 ≤ b) (hba : b < a)
    (hshort : edist p q ≤ ENNReal.ofReal b)
    (htail : ∀ s ∈ Icc 0 a, edist q (γ s) ≤ ENNReal.ofReal (a - s))
    (hmin : ∀ s ∈ Ico 0 r, edist p (γ s) = ENNReal.ofReal s) :
    r ≤ (a + b) / 2 := by
  by_contra hnot
  have hmr : (a + b) / 2 < r := lt_of_not_ge hnot
  have hma : (a + b) / 2 < a := by linarith
  obtain ⟨s, hms, hs⟩ := exists_between (lt_min hma hmr)
  have hsa : s < a := hs.trans_le (min_le_left _ _)
  have hsr : s < r := hs.trans_le (min_le_right _ _)
  have hspos : 0 < s := by linarith
  have htriangle := (edist_triangle p q (γ s)).trans
    (add_le_add hshort (htail s ⟨hspos.le, hsa.le⟩))
  rw [hmin s ⟨hspos.le, hsr⟩,
    ← ENNReal.ofReal_add hb (sub_nonneg.mpr hsa.le)] at htriangle
  have hsle : s ≤ b + (a - s) :=
    (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp htriangle
  linarith

end Poincare
