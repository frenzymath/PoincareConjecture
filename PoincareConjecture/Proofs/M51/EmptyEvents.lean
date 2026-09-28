import PoincareConjecture.Proofs.M51.EmptyIdentify
import PoincareConjecture.Proofs.M51.EmptyVanishingCopy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

include ha in
theorem event_clock (T : ℝ) (hT : T ∈ F.surgery_times) (t : ℝ) (ht : t ≤ T) :
    min t a = t := min_eq_left (ht.trans (F.surgeryTime_le_empty ha hT))

noncomputable def event (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (slice F a T).carrier] :
    SurgeryEventData F.standard_initial F.local_constants F.parameters
      (slice F a) (metric F a) T := by
  letI : Nonempty (F.slice T).carrier := by
    simpa only [slice, event_clock F ha T hT T le_rfl] using
      (inferInstance : Nonempty (slice F a T).carrier)
  exact (F.event T hT).reindexPast (fun t => min t a) (event_clock F ha T hT)

noncomputable def vanishingEvent (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (slice F a T).carrier] :
    SurgeryVanishingEventData F.parameters (slice F a) (metric F a) T := by
  letI : IsEmpty (F.slice T).carrier := by
    simpa only [slice, event_clock F ha T hT T le_rfl] using
      (inferInstance : IsEmpty (slice F a T).carrier)
  exact (F.vanishing_event T hT).reindexPast (fun t => min t a) (event_clock F ha T hT)

@[simp] theorem event_tMinus (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] [Nonempty (slice F a T).carrier] :
    (event F ha T hT).tMinus = (F.event T hT).tMinus := rfl

@[simp] theorem vanishingEvent_tMinus (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier] [IsEmpty (slice F a T).carrier] :
    (vanishingEvent F ha T hT).tMinus = (F.vanishing_event T hT).tMinus := rfl

theorem event_pre_identify_heq (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] [Nonempty (slice F a T).carrier]
    (t : Ico (F.event T hT).tMinus T)
    {x : (F.slice (F.event T hT).tMinus).carrier}
    {y : (slice F a (event F ha T hT).tMinus).carrier} (hy : HEq y x) :
    HEq ((event F ha T hT).pre_identify t y) ((F.event T hT).pre_identify t x) := by
  let E := F.event T hT
  let tau := fun t => min t a
  let hTau := event_clock F ha T hT
  have hy' : y = M51EventCopy.identify F.slice tau E.tMinus
      (hTau E.tMinus E.tMinus_lt.le) x :=
    eq_of_heq (hy.trans (M51EventCopy.identify_apply_heq F.slice tau E.tMinus
      (hTau E.tMinus E.tMinus_lt.le) x).symm)
  rw [hy']
  exact (heq_of_eq (E.reindexPast_pre_identify_apply tau hTau t x)).trans
    (M51EventCopy.identify_apply_heq F.slice tau t.1 (hTau t.1 t.2.2.le) _)

theorem vanishingEvent_pre_identify_heq (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier] [IsEmpty (slice F a T).carrier]
    (t : Ico (F.vanishing_event T hT).tMinus T)
    {x : (F.slice (F.vanishing_event T hT).tMinus).carrier}
    {y : (slice F a (vanishingEvent F ha T hT).tMinus).carrier} (hy : HEq y x) :
    HEq ((vanishingEvent F ha T hT).pre_identify t y)
      ((F.vanishing_event T hT).pre_identify t x) := by
  let E := F.vanishing_event T hT
  let tau := fun t => min t a
  let hTau := event_clock F ha T hT
  have hy' : y = M51EventCopy.identify F.slice tau E.tMinus
      (hTau E.tMinus E.tMinus_lt.le) x :=
    eq_of_heq (hy.trans (M51EventCopy.identify_apply_heq F.slice tau E.tMinus
      (hTau E.tMinus E.tMinus_lt.le) x).symm)
  rw [hy']
  exact (heq_of_eq (E.reindexPast_pre_identify_apply tau hTau t x)).trans
    (M51EventCopy.identify_apply_heq F.slice tau t.1 (hTau t.1 t.2.2.le) _)

end PoincareConjecture.M51Empty
