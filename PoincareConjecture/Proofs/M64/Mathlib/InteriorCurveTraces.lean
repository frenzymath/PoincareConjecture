import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff intervalIntegral

namespace PoincareConjecture







theorem interiorCurve_exists_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) {f d : ℝ → E}
    (hd : ∀ s ∈ Ioo a b, HasDerivAt f (d s) s)
    (hi : IntervalIntegrable d volume a b) :
    ∃ c : E, ∀ s ∈ Ioo a b, f s = c + ∫ t in a..s, d t := by
  let z := (a + b) / 2
  have hz : z ∈ Ioo a b := ⟨by dsimp [z]; linarith, by dsimp [z]; linarith⟩
  refine ⟨f z - ∫ t in a..z, d t, ?_⟩
  intro s hs
  have hsub : uIcc z s ⊆ Ioo a b := by
    rcases le_total z s with h | h
    · rw [uIcc_of_le h]
      exact Icc_subset_Ioo hz.1 hs.2
    · rw [uIcc_of_ge h]
      exact Icc_subset_Ioo hs.1 hz.2
  have hsub' : uIcc z s ⊆ uIcc a b := hsub.trans (Ioo_subset_Icc_self.trans Icc_subset_uIcc)
  have haz : IntervalIntegrable d volume a z :=
    hi.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ⟨hz.1.le, hz.2.le⟩))
  have hzs := hi.mono_set hsub'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (hsub ht)) hzs
  have hadd := intervalIntegral.integral_add_adjacent_intervals haz hzs
  rw [hFTC] at hadd
  rw [← hadd]
  abel






theorem interiorCurve_unit_trace_averages {f d : ℝ → ℝ}
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f (d s) s)
    (hi : IntervalIntegrable d volume 0 1) :
    ∃ F : ℝ → ℝ,
      AbsolutelyContinuousOnInterval F 0 1 ∧ EqOn F f (Ioo (0 : ℝ) 1) ∧
      (∀ s, F s = F 0 + ∫ t in (0 : ℝ)..s, d t) ∧
      (∫ s in Icc (0 : ℝ) 1, f s + (s - 1) * d s) = F 0 ∧
      (∫ s in Icc (0 : ℝ) 1, f s + s * d s) = F 1 := by
  obtain ⟨c, hc⟩ := interiorCurve_exists_primitive (by norm_num : (0 : ℝ) < 1) hd hi
  let F := fun s : ℝ => c + ∫ t in (0 : ℝ)..s, d t
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 1 :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  have hF : AbsolutelyContinuousOnInterval F 0 1 :=
    hconst.add (hi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc)
  have hFeq : F =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] f := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hc s hs).symm
  have hderiv : deriv F =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] d := by
    filter_upwards [ae_restrict_of_ae hi.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Icc] with s hs hsI
    exact ((hs (by simpa only [uIcc_of_le zero_le_one] using hsI)
      0 left_mem_uIcc).const_add c).deriv
  have hFi : IntegrableOn F (Icc (0 : ℝ) 1) volume :=
    (hF.continuousOn.mono (by rw [uIcc_of_le zero_le_one])).integrableOn_compact isCompact_Icc
  have hdi : IntegrableOn d (Icc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi
  have havg (q : ℝ) :
      (∫ s in Icc (0 : ℝ) 1, f s + (s + q) * d s) =
        F 1 * (1 + q) - F 0 * q := by
    let phi := fun s : ℝ => s + q
    have hphi : ContDiff ℝ 1 phi :=
      ((contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ)).add
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => q)))
    have hpderiv (s : ℝ) : deriv phi s = 1 := ((hasDerivAt_id s).add_const q).deriv
    have hb := hF.integral_mul_deriv_eq_deriv_mul hphi.contDiffOn.absolutelyContinuousOnInterval
    have heq : (∫ s in (0 : ℝ)..1, deriv F s * phi s) =
        ∫ s in (0 : ℝ)..1, d s * phi s := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le zero_le_one]
      exact (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hderiv).mono
        (fun s hs => congrArg (fun z => z * phi s) hs)
    rw [heq] at hb
    simp only [hpderiv, mul_one, phi, zero_add, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc] at hb
    have hprod : IntegrableOn (fun s => (s + q) * d s) (Icc (0 : ℝ) 1) volume :=
      hdi.continuousOn_mul (continuous_id.add continuous_const).continuousOn isCompact_Icc
    calc
      _ = ∫ s in Icc (0 : ℝ) 1, F s + (s + q) * d s :=
        integral_congr_ae (hFeq.mono fun s hs => congrArg (fun z => z + (s + q) * d s) hs.symm)
      _ = (∫ s in Icc (0 : ℝ) 1, F s) + ∫ s in Icc (0 : ℝ) 1, d s * (s + q) := by
        rw [integral_add hFi hprod]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun s => mul_comm _ _)
      _ = _ := by linarith
  refine ⟨F, hF, (fun s hs => (hc s hs).symm), ?_, ?_, ?_⟩
  · intro s
    simp only [F, intervalIntegral.integral_same, add_zero]
  · simpa only [sub_eq_add_neg, add_neg_cancel, mul_zero, mul_neg, mul_one,
      zero_sub, neg_neg, zero_add] using havg (-1)
  · simpa only [add_zero, mul_one, mul_zero, sub_zero] using havg 0





theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b c : ℝ} (h : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦
    ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hsmall : Tendsto (fun i ↦
      ∫⁻ (x : ℝ) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        _ _)
  have hsmall' := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hsmall
  refine squeeze_zero' ?_ ?_ hsmall'
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [Function.comp_apply, s]
  have hdisj : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hdisj] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_ofPred_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm
        (h.aestronglyMeasurable_restrict_uIoc.restrict),
      integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    have hcu : IntervalIntegrable f volume c (I i).1 := by
      apply IntervalIntegrable.mono_set' h
      grind [uIoc, uIcc]
    have hcv : IntervalIntegrable f volume c (I i).2 := by
      apply IntervalIntegrable.mono_set' h
      grind [uIoc, uIcc]
    rw [dist_eq_norm,
      intervalIntegral.integral_interval_sub_left hcu hcv,
      Measure.restrict_restrict_of_subset
        (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
          (Finset.mem_range.mp hi)),
      intervalIntegral.integral_symm]
    calc
      ‖-∫ x in (I i).1..(I i).2, f x‖ =
          ‖∫ x in (I i).1..(I i).2, f x‖ := norm_neg _
      _ ≤
          |∫ x in (I i).1..(I i).2, ‖f x‖| := by
        exact intervalIntegral.norm_integral_le_abs_integral_norm
      _ = ∫ x in uIoc (I i).1 (I i).2, ‖f x‖ := by
        rw [intervalIntegral.abs_intervalIntegral_eq]
        exact abs_of_nonneg (integral_nonneg (fun x => norm_nonneg (f x)))
  · intro i hi
    unfold IntegrableOn
    have h_subset :=
      AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
        (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset h_subset]
    exact IntegrableOn.mono_set h.def'.norm h_subset |>.integrable

end PoincareConjecture
