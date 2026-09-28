import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.ScalarClock.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.ScalarClock.FiniteRestart
import PoincareConjecture.Statements.M68

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture

theorem m68_finite_event_propagation
    {L U : ℝ} {E : Set ℝ} {f G : ℝ → ℝ}
    (hpiece : ∀ a b, L ≤ a → a < b → b ≤ U →
      Disjoint E (Ioo a b) → f a ≤ G a → f b ≤ G b)
    (s : Finset ℝ) :
    ∀ a b, L ≤ a → a ≤ b → b ≤ U →
      (∀ x, x ∈ Ioo a b → x ∈ E → x ∈ s) →
      f a ≤ G a → f b ≤ G b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro a b ha hab hb hcover hinit
    rcases hab.eq_or_lt with hab | hab
    · simpa [← hab] using hinit
    · apply hpiece a b ha hab hb ?_ hinit
      exact Set.disjoint_left.mpr (fun x hx hxab => by
        simpa using hcover x hxab hx)
  | @insert e s hes ih =>
    intro a b ha hab hb hcover hinit
    by_cases he : e ∈ Ioo a b
    · have hleft : f e ≤ G e := by
        apply ih a e ha he.1.le (he.2.le.trans hb) ?_ hinit
        intro x hx hxE
        have hmem := hcover x ⟨hx.1, hx.2.trans he.2⟩ hxE
        exact (Finset.mem_insert.mp hmem).resolve_left (ne_of_lt hx.2)
      apply ih e b (ha.trans he.1.le) he.2.le hb ?_ hleft
      intro x hx hxE
      have hmem := hcover x ⟨he.1.trans hx.1, hx.2⟩ hxE
      exact (Finset.mem_insert.mp hmem).resolve_left (ne_of_gt hx.1)
    · apply ih a b ha hab hb ?_ hinit
      intro x hx hxE
      have hmem := hcover x hx hxE
      exact (Finset.mem_insert.mp hmem).resolve_left (fun hxe => he (hxe ▸ hx))

theorem horizon_m68_scalar_clock_statement : M68ScalarClockStatement := by
  classical
  intro g₀ D W T P K C H B A q hM61 hM64 hM65 X HX I
  let f : ℝ → ℝ := fun x =>
    if hx : x ∈ Icc (0 : ℝ) T then X.width ⟨x, hx⟩ else 0
  have hf (t : Icc (0 : ℝ) T) : f t.1 = X.width t := by
    simp only [f, dif_pos t.property]
  have hpiece : ∀ a b, I.T₁ ≤ a → a < b → b ≤ I.T₂ →
      Disjoint D.flow.surgery_times (Ioo a b) →
      f a ≤ m68Profile I a → f b ≤ m68Profile I b := by
    intro a b ha hab hb hJ hinit
    have ha0 : 0 ≤ a := I.ordered.1.trans ha
    have haT : a ≤ T := hab.le.trans (hb.trans I.ordered.2.2)
    have hb0 : 0 ≤ b := ha0.trans hab.le
    have hbT : b ≤ T := hb.trans I.ordered.2.2
    have hcompare (c : ℝ) (hac : a < c) (hcb : c ≤ b)
        (hJc : Disjoint D.flow.surgery_times (Ioc a c)) :
        f c ≤ m68Profile I c := by
      have hinit' : X.width (M68ProfileInput.time I
          ⟨a, ⟨ha, hac.le.trans (hcb.trans hb)⟩⟩) ≤ m68Profile I a := by
        simpa only [f, dif_pos (show a ∈ Icc (0 : ℝ) T from ⟨ha0, haT⟩),
          M68ProfileInput.time] using hinit
      have hc := m68_no_event_interval_bound HX I ha0 hac (hcb.trans hb) ha hJc
        hinit' ⟨c, hac.le, le_rfl⟩
      rw [hf ⟨c, ha0.trans hac.le, hcb.trans hbT⟩]
      exact hc
    by_cases hbe : b ∈ D.flow.surgery_times
    · apply m68_event_restart_bound hab
      · intro c hc
        apply hcompare c hc.1 hc.2.le
        apply Set.disjoint_left.mpr
        intro x hxE hx
        exact Set.disjoint_left.mp hJ hxE ⟨hx.1, hx.2.trans_lt hc.2⟩
      · intro ε hε
        have hbP : b ∈ (↑P.surgery_times : Set ℝ) := by
          rw [P.surgery_times_eq]
          exact ⟨hbe, hb0, hbT⟩
        obtain ⟨δ, hδ, hbound⟩ := HX.surgery_lower_limit ⟨b, hb0, hbT⟩ hbP ε hε
        refine ⟨δ, hδ, ?_⟩
        intro c hc hnear hbefore
        have hc0T : c ∈ Icc (0 : ℝ) T :=
          ⟨ha0.trans hc.1, hc.2.trans hbT⟩
        rw [hf ⟨b, hb0, hbT⟩, hf ⟨c, hc0T⟩]
        exact hbound ⟨c, hc0T⟩ hnear hbefore
      · exact (m68_profile_equation I ⟨b, ha.trans hab.le, hb⟩).continuousAt
    · apply hcompare b hab le_rfl
      apply Set.disjoint_left.mpr
      intro x hxE hx
      rcases hx.2.eq_or_lt with hxb | hxb
      · exact hbe (hxb ▸ hxE)
      · exact Set.disjoint_left.mp hJ hxE ⟨hx.1, hxb⟩
  refine ⟨{
    clock_positive := ?_
    profile_initial := m68_profile_initial I
    profile_equation := m68_profile_equation I
    width_bound := ?_
  }⟩
  · intro t
    have ht0 : 0 ≤ t.1 := I.ordered.1.trans t.2.1
    linarith
  · intro t
    have hinit : f I.T₁ ≤ m68Profile I I.T₁ := by
      rw [m68_profile_initial I]
      exact le_of_eq (hf I.start)
    have hfinal := m68_finite_event_propagation hpiece
      (Finset.univ.image I.chronology.time) I.T₁ t.1 le_rfl t.2.1 t.2.2
      (by
        intro x hx hxE
        have hx0T : x ∈ Icc (0 : ℝ) T :=
          ⟨I.ordered.1.trans hx.1.le, hx.2.le.trans (t.2.2.trans I.ordered.2.2)⟩
        have hxP : x ∈ (↑P.surgery_times : Set ℝ) := by
          rw [P.surgery_times_eq]
          exact ⟨hxE, hx0T⟩
        have hxrange : x ∈ Set.range I.chronology.time := by
          rw [I.chronology.complete]
          exact ⟨hxP, hx.1, hx.2.trans_le t.2.2⟩
        obtain ⟨i, rfl⟩ := hxrange
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hinit
    change f (M68ProfileInput.time I t).1 ≤ m68Profile I t.1 at hfinal
    rw [hf (M68ProfileInput.time I t)] at hfinal
    exact hfinal

end PoincareConjecture
