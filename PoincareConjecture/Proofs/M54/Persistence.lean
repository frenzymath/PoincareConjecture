import PoincareConjecture.Definitions.M54GroupEffects
import Mathlib.Data.Finset.Max

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedGroupPersistence
    (F : SurgeryFlowData.{u}) (T : ℝ)
    (component : ∀ s : Set.Icc (0 : ℝ) T,
      SurgerySelectedComponent (F.slice s.1))
    (I : RepairedGroupPersistenceInput F T component) :
    Nonempty (RepairedGroupPersistenceData F T component I) := by
  classical
  have mem_times (t : ℝ) : t ∈ I.surgery_times ↔
      t ∈ F.surgery_times ∧ t ∈ Set.Icc (0 : ℝ) T := by
    change t ∈ (↑I.surgery_times : Set ℝ) ↔ _
    rw [I.surgery_times_eq]
    rfl
  have regular (a b : Set.Icc (0 : ℝ) T) (hab : a.1 ≤ b.1)
      (hdisjoint : Disjoint F.surgery_times (Set.Ioc a.1 b.1))
      (ha : Subsingleton (selectedFundamentalGroup (component a))) :
      Subsingleton (selectedFundamentalGroup (component b)) := by
    rcases hab.eq_or_lt with hab | hab
    · have : a = b := Subtype.ext hab
      cases this
      exact ha
    · obtain ⟨e⟩ := I.regular_group_equivalence a b hab hdisjoint
      let := ha
      exact e.symm.toEquiv.subsingleton
  suffices h : ∀ n : ℕ, ∀ s : Set.Icc (0 : ℝ) T,
      (I.surgery_times.filter (· ≤ s.1)).card = n →
        Subsingleton (selectedFundamentalGroup (component s)) from
    ⟨⟨fun s => h _ s rfl⟩⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hn
    let E := I.surgery_times.filter (· ≤ s.1)
    by_cases hE : E.Nonempty
    · have heE : E.max' hE ∈ E := E.max'_mem hE
      have hemem := (Finset.mem_filter.mp heE).1
      have hes := (Finset.mem_filter.mp heE).2
      let e : Set.Icc (0 : ℝ) T := ⟨E.max' hE, ((mem_times _).mp hemem).2⟩
      have he : e.1 ∈ F.surgery_times := ((mem_times _).mp hemem).1
      let hpost : Nonempty (F.slice e.1).carrier :=
        ⟨(component e).inclusion (component e).basepoint⟩
      let := hpost
      let a : Set.Icc (0 : ℝ) T :=
        ⟨(F.event e.1 he).tMinus, (F.event e.1 he).tMinus_nonnegative,
          (F.event e.1 he).tMinus_lt.le.trans e.2.2⟩
      have hae : a.1 < e.1 := (F.event e.1 he).tMinus_lt
      have haE : I.surgery_times.filter (· ≤ a.1) ⊂ E := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro t ht
          obtain ⟨ht, hta⟩ := Finset.mem_filter.mp ht
          exact Finset.mem_filter.mpr ⟨ht, hta.trans (hae.le.trans hes)⟩
        · intro hEq
          have hmem : e.1 ∈ I.surgery_times.filter (· ≤ a.1) := hEq.symm ▸ heE
          exact (not_le_of_gt hae) (Finset.mem_filter.mp hmem).2
      have hcount : (I.surgery_times.filter (· ≤ a.1)).card < n := by
        rw [← hn]
        exact Finset.card_lt_card haE
      have ha := ih _ hcount a rfl
      obtain ⟨D⟩ := I.event_factor e he hpost
      have hegroup : Subsingleton (selectedFundamentalGroup (component e)) := by
        let := ha
        exact D.target_subsingleton
      apply regular e s hes _ hegroup
      refine Set.disjoint_left.mpr ?_
      intro t ht hts
      have htE : t ∈ E := Finset.mem_filter.mpr
        ⟨(mem_times t).mpr ⟨ht, e.2.1.trans hts.1.le, hts.2.trans s.2.2⟩, hts.2⟩
      exact (not_le_of_gt hts.1) (E.le_max' t htE)
    · apply regular ⟨0, le_rfl, I.time_nonnegative⟩ s s.2.1 _ I.initial_group
      refine Set.disjoint_left.mpr ?_
      intro t ht hts
      exact hE ⟨t, Finset.mem_filter.mpr
        ⟨(mem_times t).mpr ⟨ht, hts.1.le, hts.2.trans s.2.2⟩, hts.2⟩⟩

end PoincareConjecture
