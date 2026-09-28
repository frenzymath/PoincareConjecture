import PoincareConjecture.Definitions.M49VolumeLoss

set_option autoImplicit false

universe u

namespace PoincareConjecture.M49

noncomputable def eventCapCount (F : SurgeryFlowData.{u}) (T : ℝ) : ℕ := by
  classical
  exact if hT : T ∈ F.surgery_times then
    if hN : Nonempty (F.slice T).carrier then
      letI := hN
      (F.event T hT).cap_count
    else 0
  else 0

noncomputable def eventDeletionCount (F : SurgeryFlowData.{u}) (T : ℝ) : ℕ := by
  classical
  exact if T ∈ F.surgery_times ∧ eventCapCount F T = 0 then 1 else 0

theorem eventCapCount_eq (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] : eventCapCount F T = (F.event T hT).cap_count := by
  simp only [eventCapCount, dif_pos hT, dif_pos (inferInstance : Nonempty (F.slice T).carrier)]

theorem eventCapCount_eq_zero_of_isEmpty (F : SurgeryFlowData.{u}) (T : ℝ)
    [IsEmpty (F.slice T).carrier] : eventCapCount F T = 0 := by
  classical
  simp [eventCapCount, not_nonempty_iff.mpr (inferInstance : IsEmpty (F.slice T).carrier)]

theorem eventDeletionCount_eq (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times) :
    eventDeletionCount F T = if eventCapCount F T = 0 then 1 else 0 := by
  simp only [eventDeletionCount, hT, true_and]

theorem one_le_event_counts (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times) :
    1 ≤ eventCapCount F T + eventDeletionCount F T := by
  rw [eventDeletionCount_eq F T hT]
  split_ifs with h <;> omega

end PoincareConjecture.M49
