/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/FiniteChartCommonTimeNative.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Common positive time for finitely many local windows

Finite chart constructions generally produce one positive lifespan per chart.
This elementary finite minimum argument chooses a single positive time below
all of them.  It is independent of the metric decoder and of the parabolic
fixed-point construction.
-/

set_option autoImplicit false

namespace PoincareMT

theorem exists_common_positive_time
    {alpha : Type _} (s : Finset alpha) (tau : alpha → ℝ)
    (hτ : ∀ a ∈ s, 0 < tau a) :
    ∃ T : ℝ, 0 < T ∧ ∀ a ∈ s, T ≤ tau a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro a ha
      simp at ha
  | @insert a s ha ih =>
      have hτs : ∀ b ∈ s, 0 < tau b := by
        intro b hb
        exact hτ b (by simp [hb])
      obtain ⟨T, hT, hTs⟩ := ih hτs
      refine ⟨min T (tau a), lt_min hT (hτ a (by simp)), ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hTs b hb)

end PoincareMT
