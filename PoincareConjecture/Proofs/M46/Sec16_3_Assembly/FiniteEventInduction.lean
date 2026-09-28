import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Data.Real.Basic

set_option autoImplicit false

open Set

namespace PoincareConjecture.Proofs.M46

private theorem propagation_from_event_values {a b : ℝ} {S : Set ℝ}
    (hab : a ≤ b) (hfinite : (S ∩ Ioc a b).Finite) (Q : ℝ → Prop) (ha : Q a)
    (hordinary : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      Disjoint S (Ioc s t) → Q s → Q t)
    (hevents : ∀ t ∈ S ∩ Ioc a b, Q t) : Q b := by
  classical
  by_cases hn : (S ∩ Ioc a b).Nonempty
  · obtain ⟨t, ht, hmax⟩ := (S ∩ Ioc a b).exists_max_image id hfinite hn
    apply hordinary t ⟨ht.2.1.le, ht.2.2⟩ b ⟨hab, le_rfl⟩ ht.2.2
    · apply Set.disjoint_left.mpr
      intro s hs hst
      exact (hmax s ⟨hs, ht.2.1.trans hst.1, hst.2⟩).not_gt hst.1
    · exact hevents t ht
  · apply hordinary a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
    · exact Set.disjoint_left.mpr (fun t ht htab => hn ⟨t, ht, htab⟩)
    · exact ha

theorem finite_event_forward_induction {a b : ℝ} {S : Set ℝ}
    (hab : a ≤ b) (hfinite : (S ∩ Ioc a b).Finite) (Q : ℝ → Prop) (ha : Q a)
    (hordinary : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      Disjoint S (Ioc s t) → Q s → Q t)
    (hevent : ∀ t ∈ S ∩ Ioc a b, (∀ s ∈ Ico a t, Q s) → Q t) :
    Q b := by
  have hevents : ∀ t ∈ S ∩ Ioc a b, Q t := by
    intro t ht
    refine hfinite.isWF.induction ht ?_
    intro t ht ih
    apply hevent t ht
    intro s hs
    have hsb : s ≤ b := hs.2.le.trans ht.2.2
    have hsmall : (S ∩ Ioc a s).Finite := hfinite.subset
      (fun u hu => ⟨hu.1, hu.2.1, hu.2.2.trans hsb⟩)
    apply propagation_from_event_values hs.1 hsmall Q ha
    · intro u hu v hv huv hfree hQu
      exact hordinary u ⟨hu.1, hu.2.trans hsb⟩ v ⟨hv.1, hv.2.trans hsb⟩
        huv hfree hQu
    · intro u hu
      exact ih u ⟨hu.1, hu.2.1, hu.2.2.trans hsb⟩ (hu.2.2.trans_lt hs.2)
  exact propagation_from_event_values hab hfinite Q ha hordinary hevents

end PoincareConjecture.Proofs.M46
