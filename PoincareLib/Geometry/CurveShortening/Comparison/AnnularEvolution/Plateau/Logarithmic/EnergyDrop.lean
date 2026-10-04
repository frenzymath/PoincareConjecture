import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Polar.AnnularEnergy
import Mathlib.MeasureTheory.Integral.Average

/-!
# Selecting an actual small-energy logarithmic circle

The finite telescope selects a shell. The first-moment estimate then
selects a radius outside every exceptional null set needed for its trace.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PoincareMT

/-- A finite energy telescope contains an actual shell whose drop is no larger than the
average. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64_exists_small_energy_drop (E : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    (hEN : 0 ≤ E N) :
    ∃ j < N, E j - E (j + 1) ≤ E 0 / N := by
  have htel (n : ℕ) : (∑ j ∈ Finset.range n, (E j - E (j + 1))) = E 0 - E n := by
    induction n with
    | zero => simp
    | succ n hn => rw [Finset.sum_range_succ, hn]; ring
  have hsum : (∑ j ∈ Finset.range N, (E j - E (j + 1))) ≤
      ∑ _j ∈ Finset.range N, E 0 / N := by
    rw [htel]
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hNr]
    linarith
  obtain ⟨j, hj, hjE⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hN.ne') hsum
  exact ⟨j, Finset.mem_range.mp hj, hjE⟩

/-- Choose an actual unit-interval point below the integral while retaining every supplied
almost-everywhere property. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem m64UnitInterval_exists_le_integral_of_ae
    (f : ℝ → ℝ) (hf : IntegrableOn f (Icc (0 : ℝ) 1))
    {P : ℝ → Prop} (hP : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), P s) :
    ∃ s ∈ Icc (0 : ℝ) 1, P s ∧
      f s ≤ ∫ t in Icc (0 : ℝ) 1, f t := by
  let : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have hgood : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), s ∈ Icc (0 : ℝ) 1 ∧ P s :=
    (ae_restrict_mem measurableSet_Icc).and hP
  have hnull : (volume.restrict (Icc (0 : ℝ) 1))
      {s | ¬(s ∈ Icc (0 : ℝ) 1 ∧ P s)} = 0 := by
    simpa only [ae_iff] using hgood
  obtain ⟨s, hs, hsf⟩ := exists_notMem_null_le_integral hf hnull
  have hsP : s ∈ Icc (0 : ℝ) 1 ∧ P s := not_not.mp hs
  exact ⟨s, hsP.1, hsP.2, hsf⟩

end PoincareMT
