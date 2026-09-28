import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Basic









set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace Poincare.MeasureTheory

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [BorelSpace X]



theorem card_mul_le_measure_of_separated_balls
    (μ : Measure X) (s : Finset X) {r v : ℝ≥0∞} {U : Set X}
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r + r ≤ edist x y)
    (hsub : ∀ x ∈ s, Metric.eball x r ⊆ U)
    (hvol : ∀ x ∈ s, v ≤ μ (Metric.eball x r)) :
    (s.card : ℝ≥0∞) * v ≤ μ U := by
  have hdisj : (s : Set X).PairwiseDisjoint (fun x => Metric.eball x r) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hxz hyz
    have htri := edist_triangle x z y
    have hsmall : edist x z + edist z y < r + r := by
      exact ENNReal.add_lt_add (by simpa only [Metric.mem_eball, edist_comm] using hxz) hyz
    exact (not_lt_of_ge (hsep x hx y hy hxy)) (htri.trans_lt hsmall)
  calc
    (s.card : ℝ≥0∞) * v = ∑ x ∈ s, v := by simp
    _ ≤ ∑ x ∈ s, μ (Metric.eball x r) := Finset.sum_le_sum hvol
    _ = μ (⋃ x ∈ s, Metric.eball x r) :=
      (measure_biUnion_finset hdisj (fun _ _ => Metric.isOpen_eball.measurableSet)).symm
    _ ≤ μ U := measure_mono (iUnion₂_subset hsub)



theorem card_le_measure_div_of_separated_balls
    (μ : Measure X) (s : Finset X) {r : ℝ≥0∞} {v : ℝ} {U : Set X}
    (hv : 0 < v) (hU : μ U ≠ ⊤)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r + r ≤ edist x y)
    (hsub : ∀ x ∈ s, Metric.eball x r ⊆ U)
    (hvol : ∀ x ∈ s, ENNReal.ofReal v ≤ μ (Metric.eball x r)) :
    (s.card : ℝ) ≤ (μ U).toReal / v := by
  have h := card_mul_le_measure_of_separated_balls μ s hsep hsub hvol
  have hreal := ENNReal.toReal_mono hU h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hv.le] at hreal
  exact (le_div_iff₀ hv).mpr hreal



theorem card_le_inv_of_relative_ball_measure
    (μ : Measure X) (s : Finset X) {r : ℝ≥0∞} {c : ℝ} {U : Set X}
    (hc : 0 < c) (hU0 : μ U ≠ 0) (hU : μ U ≠ ⊤)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r + r ≤ edist x y)
    (hsub : ∀ x ∈ s, Metric.eball x r ⊆ U)
    (hvol : ∀ x ∈ s, ENNReal.ofReal c * μ U ≤ μ (Metric.eball x r)) :
    (s.card : ℝ) ≤ c⁻¹ := by
  have h := card_mul_le_measure_of_separated_balls μ s hsep hsub hvol
  have hreal := ENNReal.toReal_mono hU h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hc.le] at hreal
  have hpositive : 0 < (μ U).toReal := ENNReal.toReal_pos hU0 hU
  have hcard : (s.card : ℝ) * c ≤ 1 := by
    apply (mul_le_mul_iff_left₀ hpositive).mp
    simpa only [mul_assoc, one_mul] using hreal
  simpa only [one_div] using (le_div_iff₀ hc).mpr hcard

end Poincare.MeasureTheory
