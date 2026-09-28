import PoincareConjecture.Proofs.M65.Mathlib.EnergyBadTimes









set_option autoImplicit false

open MeasureTheory Set
open scoped intervalIntegral BigOperators

namespace PoincareConjecture.M65




theorem energy_badIntervals_sum_le {ι : Type*} {indices : Finset ι}
    {left right : ι → ℝ} {energy : ℝ → ℝ} {a b C B : ℝ}
    (hab : a ≤ b) (hnonneg : ∀ t, 0 ≤ energy t)
    (hintegrable : IntervalIntegrable energy volume a b)
    (hbound : (∫ t in a..b, energy t) ≤ C) (hB : 0 < B)
    (horder : ∀ i ∈ indices, left i ≤ right i)
    (hslab : ∀ i ∈ indices, Ioo (left i) (right i) ⊆ Icc a b)
    (hbad : ∀ i ∈ indices, ∀ t ∈ Ioo (left i) (right i), B < energy t)
    (hdisjoint : (indices : Set ι).PairwiseDisjoint (fun i => Ioo (left i) (right i))) :
    (∑ i ∈ indices, (right i - left i)) ≤ C / B := by
  have hfinite : volume {t | t ∈ Icc a b ∧ B < energy t} ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono fun _ ht => ht.1)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hsubset : (⋃ i ∈ indices, Ioo (left i) (right i)) ⊆
      {t | t ∈ Icc a b ∧ B < energy t} := by
    intro t ht
    obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨hslab i hi ht, hbad i hi t ht⟩
  calc
    _ = ∑ i ∈ indices, volume.real (Ioo (left i) (right i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Real.volume_real_Ioo_of_le (horder i hi)).symm
    _ = volume.real (⋃ i ∈ indices, Ioo (left i) (right i)) := by
      exact (measureReal_biUnion_finset hdisjoint (fun _ _ => measurableSet_Ioo)
        (fun _ _ => by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).symm
    _ ≤ volume.real {t | t ∈ Icc a b ∧ B < energy t} :=
      measureReal_mono hsubset hfinite
    _ ≤ C / B := energy_badTimes_measure_le hab hnonneg hintegrable hbound hB

end PoincareConjecture.M65
