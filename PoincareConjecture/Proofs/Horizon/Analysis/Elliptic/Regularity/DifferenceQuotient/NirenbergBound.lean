import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.WeakBound
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.TestFunction.Standard
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.CrossTerms.Principal

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal

namespace Poincare.Analysis.Sobolev

open NirenbergCrossBoundsNonSmooth NirenbergStandardTest

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private lemma memLp_continuous_compactSupport_mul
    {a v : E → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hv : MemLp v 2 volume) : MemLp (fun x => a x * v x) 2 volume := by
  obtain ⟨C, _, hC⟩ := exists_bound_of_continuous_compactSupport ha hac
  exact memLp_bounded_mul ha.aestronglyMeasurable hC hv

private lemma cutoff_product_sq_bound
    {a b z t N : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : |b| ≤ N) :
    (a ^ 2 * t + 2 * a * b * z) ^ 2 ≤
      8 * N ^ 2 * z ^ 2 + 2 * a ^ 2 * t ^ 2 := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  have hb2 : b ^ 2 ≤ N ^ 2 := by
    have hN : 0 ≤ N := (abs_nonneg b).trans hb
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hab : a ^ 2 * b ^ 2 ≤ N ^ 2 :=
    (mul_le_mul_of_nonneg_right ha2 (sq_nonneg b)).trans (by simpa using hb2)
  have hz := mul_le_mul_of_nonneg_right hab (sq_nonneg z)
  have hat := mul_le_mul_of_nonneg_right ha2 (mul_nonneg (sq_nonneg a) (sq_nonneg t))
  nlinarith [sq_nonneg (a ^ 2 * t - 2 * a * b * z)]

theorem nirenbergTestFunction_sq_integral_le_weak
    {u g : E → ℝ} (hu : MemLp u 2 volume) (hg : MemLp g 2 volume)
    (k : Fin d) (hweak : Weak.HasWeakPartialDeriv k g u Set.univ)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηrange : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {h : ℝ} (hh : h ≠ 0) :
    ∫ x, (NirenbergTestFunction.nirenbergTestFunction k h η u x) ^ 2 ≤
      8 * N ^ 2 * (∫ x in tsupport η, (diffQuot k h u x) ^ 2) +
      2 * (∫ x, (η x) ^ 2 * (diffQuot k h g x) ^ 2) := by
  let q : E → ℝ := fun x => η x ^ 2 * diffQuot k h u x
  let a : E → ℝ := fun x =>
    (fderiv ℝ (fun y => η y ^ 2) x) (EuclideanSpace.single k 1)
  let G : E → ℝ := fun x => η x ^ 2 * diffQuot k h g x + a x * diffQuot k h u x
  have hη2c : HasCompactSupport (fun x => η x ^ 2) := by
    simp only [pow_two]
    exact hηc.mul_right
  have hdqu := memLp_diffQuot_two k h hu
  have hdqg := memLp_diffQuot_two k h hg
  have hq : MemLp q 2 volume :=
    memLp_continuous_compactSupport_mul (hη.continuous.pow 2) hη2c hdqu
  have hac : HasCompactSupport a := hη2c.fderiv_apply (𝕜 := ℝ) _
  have ha : Continuous a :=
    ((hη.pow 2).continuous_fderiv (by simp)).clm_apply continuous_const
  have hG : MemLp G 2 volume :=
    (memLp_continuous_compactSupport_mul (hη.continuous.pow 2) hη2c hdqg).add
      (memLp_continuous_compactSupport_mul ha hac hdqu)
  have hqweak : Weak.HasWeakPartialDeriv k G q Set.univ := by
    exact NirenbergDiffQuotTestFunction.hasWeakPartialDeriv_eta_sq_diffQuot k k h hη
      (by simpa using hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      (by simpa using hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hweak
  let v := standardNirenbergTest k h η u
  have hvc : HasCompactSupport v := standardNirenbergTest_hasCompactSupport k h hηc u
  have hbase := integral_sq_diffQuot_le_integral_sq_weakPartial_meas hq hG k hqweak
    MeasurableSet.univ (isClosed_tsupport v).measurableSet
    (by simpa only [(isClosed_tsupport v).closure_eq] using hvc.isCompact :
      IsCompact (closure (tsupport v)))
    (show 0 < |h| + 1 by positivity) (Set.subset_univ _)
    (neg_ne_zero.mpr hh) (show |-h| ≤ |h| + 1 by rw [abs_neg]; linarith)
  have hbase' : ∫ x, v x ^ 2 ≤ ∫ x, G x ^ 2 := by
    change ∫ x in tsupport v, v x ^ 2 ≤ ∫ x in Set.univ, G x ^ 2 at hbase
    rw [Measure.restrict_univ,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; norm_num)] at hbase
    exact hbase
  have ha_formula (x : E) : a x =
      2 * η x * (fderiv ℝ η x) (EuclideanSpace.single k 1) := by
    dsimp [a]
    rw [fderiv_fun_pow 2 (hη.differentiable (by simp) x)]
    rw [smul_apply]
    norm_num only [Nat.reduceSub, pow_one]
    rw [two_smul, smul_eq_mul]
    ring
  have hpoint (x : E) : G x ^ 2 ≤
      8 * N ^ 2 * (tsupport η).indicator (fun y => (diffQuot k h u y) ^ 2) x +
      2 * (η x) ^ 2 * (diffQuot k h g x) ^ 2 := by
    dsimp [G]
    rw [ha_formula]
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx]
      apply cutoff_product_sq_bound (hηrange ⟨x, rfl⟩)
      have hb := (fderiv ℝ η x).le_opNorm (EuclideanSpace.single k 1)
      simpa [Real.norm_eq_abs] using hb.trans (by simpa using hN x)
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  have hG2 : Integrable (fun x => G x ^ 2) volume := by
    simpa only [Pi.mul_def, pow_two] using hG.integrable_mul hG
  have hdu2 : Integrable (fun x => diffQuot k h u x ^ 2) volume := by
    simpa only [Pi.mul_def, pow_two] using hdqu.integrable_mul hdqu
  have hηdqg : MemLp (fun x => η x * diffQuot k h g x) 2 volume :=
    memLp_continuous_compactSupport_mul hη.continuous hηc hdqg
  have hη2dqg2 : Integrable (fun x => η x ^ 2 * diffQuot k h g x ^ 2) volume := by
    convert hηdqg.integrable_mul hηdqg using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hfirst := (hdu2.indicator (isClosed_tsupport η).measurableSet).const_mul (8 * N ^ 2)
  have hsecond : Integrable (fun x => 2 * η x ^ 2 * diffQuot k h g x ^ 2) volume := by
    simpa only [mul_assoc] using hη2dqg2.const_mul 2
  have hbound := integral_mono hG2 (hfirst.add hsecond) hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_add hfirst hsecond, integral_const_mul,
    integral_indicator (isClosed_tsupport η).measurableSet] at hbound
  have hsecond_eq : ∫ x, 2 * η x ^ 2 * diffQuot k h g x ^ 2 =
      2 * ∫ x, η x ^ 2 * diffQuot k h g x ^ 2 := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  rw [hsecond_eq] at hbound
  exact hbase'.trans hbound

end Poincare.Analysis.Sobolev
