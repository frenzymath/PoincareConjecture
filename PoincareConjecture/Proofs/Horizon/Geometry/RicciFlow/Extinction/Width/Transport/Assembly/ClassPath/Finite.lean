import Mathlib.Data.Finset.Max
import Mathlib.Order.WellFoundedSet

set_option autoImplicit false

open Set

universe u v

namespace PoincareConjecture

def M67OrdinaryBetween {J : Type u} [LinearOrder J] (events : Finset J)
    (a b : J) : Prop := a ≤ b ∧ Disjoint (↑events : Set J) (Ioc a b)

theorem M67OrdinaryBetween.refl {J : Type u} [LinearOrder J]
    (events : Finset J) (a : J) : M67OrdinaryBetween events a a := by
  simp [M67OrdinaryBetween]

theorem M67OrdinaryBetween.trans {J : Type u} [LinearOrder J]
    {events : Finset J} {a b c : J}
    (hab : M67OrdinaryBetween events a b) (hbc : M67OrdinaryBetween events b c) :
    M67OrdinaryBetween events a c := by
  refine ⟨hab.1.trans hbc.1, Set.disjoint_left.mpr ?_⟩
  intro t ht htc
  by_cases htb : t ≤ b
  · exact Set.disjoint_left.mp hab.2 ht ⟨htc.1, htb⟩
  · exact Set.disjoint_left.mp hbc.2 ht ⟨lt_of_not_ge htb, htc.2⟩

theorem m67_finite_transport_section
    {J : Type u} [LinearOrder J] (zero : J) (hzero : ∀ t : J, zero ≤ t)
    (events : Finset J) (hzero_event : zero ∉ events)
    (before : ∀ s : J, s ∈ events → J)
    (before_lt : ∀ s hs, before s hs < s)
    (U : J → Type v) (initial : U zero)
    (regular : ∀ a b, M67OrdinaryBetween events a b → U a → U b)
    (regular_refl : ∀ a h x, regular a a h x = x)
    (regular_trans : ∀ a b c hab hbc x,
      regular b c hbc (regular a b hab x) =
        regular a c (hab.trans hbc) x)
    (event : ∀ s hs, U (before s hs) → U s) :
    ∃ sol : ∀ t, U t,
      sol zero = initial ∧
      (∀ a b h, regular a b h (sol a) = sol b) ∧
      (∀ s hs, sol s = event s hs (sol (before s hs))) := by
  classical
  let stages : Finset J := insert zero events
  let Stage := {t : J // t ∈ stages}
  let lastSet (t : J) : Finset J := stages.filter (· ≤ t)
  have hlastNonempty (t : J) : (lastSet t).Nonempty :=
    ⟨zero, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hzero t⟩⟩
  let last (t : J) : Stage :=
    ⟨(lastSet t).max' (hlastNonempty t),
      (Finset.mem_filter.mp ((lastSet t).max'_mem (hlastNonempty t))).1⟩
  have last_le (t : J) : (last t).val ≤ t :=
    (Finset.mem_filter.mp ((lastSet t).max'_mem (hlastNonempty t))).2
  have le_last (s : Stage) (t : J) (hst : s.val ≤ t) : s.val ≤ (last t).val :=
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨s.property, hst⟩)
  have last_stage (s : Stage) : last s.val = s := by
    apply Subtype.ext
    exact le_antisymm (last_le _) (le_last s s.val le_rfl)
  have last_regular (t : J) : M67OrdinaryBetween events (last t).val t := by
    refine ⟨last_le t, Set.disjoint_left.mpr ?_⟩
    intro s hs hst
    have hstage : s ∈ stages := Finset.mem_insert_of_mem hs
    exact (not_lt_of_ge (le_last ⟨s, hstage⟩ t hst.2)) hst.1
  have stage_event (s : Stage) (hs : s.val ≠ zero) : s.val ∈ events :=
    (Finset.mem_insert.mp s.property).resolve_left hs
  have hwf : WellFounded ((· < ·) : Stage → Stage → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  let seed : ∀ s : Stage, U s.val := hwf.fix fun s rec =>
    if hs : s.val = zero then hs.symm ▸ initial
    else event s.val (stage_event s hs)
      (regular (last (before s.val (stage_event s hs))).val
        (before s.val (stage_event s hs)) (last_regular _)
        (rec (last (before s.val (stage_event s hs)))
          ((last_le _).trans_lt (before_lt s.val (stage_event s hs)))))
  have seed_zero (s : Stage) (hs : s.val = zero) : seed s = hs.symm ▸ initial := by
    rw [show seed s = _ from hwf.fix_eq _ s]
    rw [dif_pos hs]
  have seed_event (s : Stage) (hs : s.val ∈ events) :
      seed s = event s.val hs
        (regular (last (before s.val hs)).val (before s.val hs) (last_regular _)
          (seed (last (before s.val hs)))) := by
    have hne : s.val ≠ zero := fun h => hzero_event (h ▸ hs)
    rw [show seed s = _ from hwf.fix_eq _ s]
    rw [dif_neg hne]
  let sol (t : J) : U t := regular (last t).val t (last_regular t) (seed (last t))
  have regular_seed_congr (a b : Stage) (h : a = b) (t : J)
      (ha : M67OrdinaryBetween events a.val t)
      (hb : M67OrdinaryBetween events b.val t) :
      regular a.val t ha (seed a) = regular b.val t hb (seed b) := by
    subst b
    rfl
  have section_stage (s : Stage) : sol s.val = seed s := by
    exact (regular_seed_congr (last s.val) s (last_stage s) s.val
      (last_regular s.val) (M67OrdinaryBetween.refl events s.val)).trans
        (regular_refl _ _ _)
  refine ⟨sol, ?_, ?_, ?_⟩
  · have h := section_stage ⟨zero, Finset.mem_insert_self _ _⟩
    exact h.trans (seed_zero _ rfl)
  · intro a b hab
    have hl : last a = last b := by
      apply Subtype.ext
      apply le_antisymm
      · exact le_last (last a) b ((last_le a).trans hab.1)
      · apply le_last (last b) a
        by_contra hn
        have hn' : a < (last b).val := lt_of_not_ge hn
        have hne : (last b).val ≠ zero := by
          intro h
          exact (not_lt_of_ge (hzero a)) (h ▸ hn')
        exact Set.disjoint_left.mp hab.2 (stage_event (last b) hne)
          ⟨hn', last_le b⟩
    dsimp only [sol]
    exact (regular_trans _ _ _ _ _ _).trans
      (regular_seed_congr (last a) (last b) hl b
        ((last_regular a).trans hab) (last_regular b))
  · intro s hs
    exact (section_stage ⟨s, Finset.mem_insert_of_mem hs⟩).trans
      (seed_event ⟨s, Finset.mem_insert_of_mem hs⟩ hs)

end PoincareConjecture
