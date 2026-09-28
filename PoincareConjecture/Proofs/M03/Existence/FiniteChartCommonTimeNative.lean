import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace PoincareConjecture

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

end PoincareConjecture
