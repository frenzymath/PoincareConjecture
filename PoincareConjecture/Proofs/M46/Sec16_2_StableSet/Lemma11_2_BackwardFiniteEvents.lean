import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Data.Real.Basic










set_option autoImplicit false

open Set

namespace PoincareConjecture.Proofs.M46



theorem backward_cylinder_finite_event_induction {a b : ℝ} {events : Set ℝ}
    (hab : a ≤ b) (hfinite : (events ∩ Ioc a b).Finite) (Q : ℝ → Prop)
    (hb : Q b)
    (hordinary : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      Disjoint events (Ioc s t) → Q t → Q s)
    (hevent : ∀ t ∈ events ∩ Ioc a b, Q t →
      ∃ s ∈ Icc a t, s < t ∧ Q s) :
    Q a := by
  classical
  have hevents : ∀ t ∈ events ∩ Ioc a b, Q t → Q a := by
    intro t ht
    refine hfinite.isWF.induction (P := fun t => Q t → Q a) ht ?_
    intro t ht ih hQt
    obtain ⟨s, hs, hst, hQs⟩ := hevent t ht hQt
    have hsb : s ≤ b := hs.2.trans ht.2.2
    have hsmall : (events ∩ Ioc a s).Finite := hfinite.subset
      (fun u hu => ⟨hu.1, hu.2.1, hu.2.2.trans hsb⟩)
    by_cases hn : (events ∩ Ioc a s).Nonempty
    · obtain ⟨u, hu, hmax⟩ := (events ∩ Ioc a s).exists_max_image id hsmall hn
      have hfree : Disjoint events (Ioc u s) := by
        apply Set.disjoint_left.mpr
        intro v hv hvI
        exact (hmax v ⟨hv, hu.2.1.trans hvI.1, hvI.2⟩).not_gt hvI.1
      exact ih u ⟨hu.1, hu.2.1, hu.2.2.trans hsb⟩ (hu.2.2.trans_lt hst)
        (hordinary u ⟨hu.2.1.le, hu.2.2.trans hsb⟩ s ⟨hs.1, hsb⟩
          hu.2.2 hfree hQs)
    · exact hordinary a ⟨le_rfl, hab⟩ s ⟨hs.1, hsb⟩ hs.1
        (Set.disjoint_left.mpr (fun u hu huI => hn ⟨u, hu, huI⟩)) hQs
  by_cases hn : (events ∩ Ioc a b).Nonempty
  · obtain ⟨t, ht, hmax⟩ := (events ∩ Ioc a b).exists_max_image id hfinite hn
    have hfree : Disjoint events (Ioc t b) := by
      apply Set.disjoint_left.mpr
      intro s hs hsI
      exact (hmax s ⟨hs, ht.2.1.trans hsI.1, hsI.2⟩).not_gt hsI.1
    exact hevents t ht
      (hordinary t ⟨ht.2.1.le, ht.2.2⟩ b ⟨hab, le_rfl⟩ ht.2.2 hfree hb)
  · exact hordinary a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
      (Set.disjoint_left.mpr (fun t ht htI => hn ⟨t, ht, htI⟩)) hb

end PoincareConjecture.Proofs.M46
