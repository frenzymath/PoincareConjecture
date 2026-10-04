import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossData

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/FlowEventCounts.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Counts attached to the actual raw surgery events

Morgan-Tian Lemma 17.12, pp. 410-411. The number of inserted caps
counts sphere cuts, while zero-cap and vanishing events contribute
one deletion count. Off the actual event set both counts are zero.
See M49 derivation 32 for the exact dependent selector semantics.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.SurgeryVolume

/-- The actual cap multiplicity, with zero at vanishing and non-event
times (MT Lemma 17.12, pp. 410-411). -/
noncomputable def eventCapCount (F : SurgeryFlowData.{u}) (T : ℝ) : ℕ := by
  classical
  exact if hT : T ∈ F.surgery_times then
    if hN : Nonempty (F.slice T).carrier then
      letI := hN
      (F.event T hT).cap_count
    else 0
  else 0

/-- Zero-cap actual events, including vanishing events, contribute one
deletion count (MT Lemma 17.12, pp. 410-411). -/
noncomputable def eventDeletionCount (F : SurgeryFlowData.{u}) (T : ℝ) : ℕ := by
  classical
  exact if T ∈ F.surgery_times ∧ eventCapCount F T = 0 then 1 else 0

/-- At an actual nonempty event the total count is its literal cap_count
(MT Lemma 17.12, pp. 410-411). -/
theorem eventCapCount_eq (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] : eventCapCount F T = (F.event T hT).cap_count := by
  simp only [eventCapCount, dif_pos hT, dif_pos (inferInstance : Nonempty (F.slice T).carrier)]

/-- Empty slices have no cap count, whether or not the time is an event
(MT Lemma 17.12, pp. 410-411). -/
theorem eventCapCount_eq_zero_of_isEmpty (F : SurgeryFlowData.{u}) (T : ℝ)
    [IsEmpty (F.slice T).carrier] : eventCapCount F T = 0 := by
  classical
  simp [eventCapCount, not_nonempty_iff.mpr (inferInstance : IsEmpty (F.slice T).carrier)]

/-- The deletion indicator at an event is exactly its zero-cap test
(MT Lemma 17.12, pp. 410-411). -/
theorem eventDeletionCount_eq (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times) :
    eventDeletionCount F T = if eventCapCount F T = 0 then 1 else 0 := by
  simp only [eventDeletionCount, hT, true_and]

/-- Each actual event contributes at least one cut or deletion count
(MT Lemma 17.12, pp. 410-411). -/
theorem one_le_event_counts (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times) :
    1 ≤ eventCapCount F T + eventDeletionCount F T := by
  rw [eventDeletionCount_eq F T hT]
  split_ifs with h <;> omega

end PoincareMT.SurgeryVolume
