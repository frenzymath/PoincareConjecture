import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false

open Set

namespace Poincare

theorem finite_event_induction {α : Type*} [LinearOrder α]
    (S : Finset α) {a b : α} (hS : (S : Set α) ⊆ Ioc a b)
    (Q : α → Prop) (hinit : Q a)
    (hregular : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t →
      Disjoint (S : Set α) (Ioc s t) → Q s → Q t)
    (hevent : ∀ t ∈ S, (∀ s ∈ Ico a t, Q s) → Q t) :
    ∀ t ∈ Icc a b, Q t := by
  classical
  induction S using Finset.induction_on_min generalizing a b with
  | empty =>
      intro t ht
      rcases ht.1.eq_or_lt with heq | hlt
      · simpa only [← heq] using hinit
      · exact hregular a ⟨le_rfl, ht.1.trans ht.2⟩ t ht hlt (by simp) hinit
  | insert z S hmin ih =>
      have hz : z ∈ Ioc a b := hS (by simp)
      have hbefore : ∀ t ∈ Ico a z, Q t := by
        intro t ht
        rcases ht.1.eq_or_lt with heq | hlt
        · simpa only [← heq] using hinit
        · apply hregular a ⟨le_rfl, hz.1.le.trans hz.2⟩ t
            ⟨ht.1, ht.2.le.trans hz.2⟩ hlt _ hinit
          apply Set.disjoint_left.mpr
          intro x hx hxt
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact (not_le_of_gt ht.2) hxt.2
          · exact (not_lt_of_ge (hxt.2.trans ht.2.le)) (hmin x hx)
      have hQz : Q z := hevent z (by simp) hbefore
      have hS' : (S : Set α) ⊆ Ioc z b := by
        intro x hx
        exact ⟨hmin x hx, (hS (Finset.mem_insert_of_mem hx)).2⟩
      have hregular' : ∀ s ∈ Icc z b, ∀ t ∈ Icc z b, s < t →
          Disjoint (S : Set α) (Ioc s t) → Q s → Q t := by
        intro s hs t ht hst hfree hQs
        apply hregular s ⟨hz.1.le.trans hs.1, hs.2⟩ t
          ⟨hz.1.le.trans ht.1, ht.2⟩ hst _ hQs
        apply Set.disjoint_left.mpr
        intro x hx hxt
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact (not_lt_of_ge hs.1) hxt.1
        · exact Set.disjoint_left.mp hfree hx hxt
      have hevent' : ∀ t ∈ S, (∀ s ∈ Ico z t, Q s) → Q t := by
        intro t ht hprev
        apply hevent t (Finset.mem_insert_of_mem ht)
        intro s hs
        by_cases hsz : s < z
        · exact hbefore s ⟨hs.1, hsz⟩
        · exact hprev s ⟨le_of_not_gt hsz, hs.2⟩
      intro t ht
      by_cases htz : t < z
      · exact hbefore t ⟨ht.1, htz⟩
      · exact ih hS' hQz hregular' hevent' t ⟨le_of_not_gt htz, ht.2⟩

end Poincare
