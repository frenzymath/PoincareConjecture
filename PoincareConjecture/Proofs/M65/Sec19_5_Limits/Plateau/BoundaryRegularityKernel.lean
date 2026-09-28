import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityPotential
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

open Set Metric MeasureTheory Complex
open scoped Topology

namespace PoincareConjecture.M65Boundary

private theorem integrable_power_tail {b : ℝ} (hb : 1 < b) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (-b - 1)) (closedBall 0 2)ᶜ := by
  let f : ℝ → ℝ := (Ioi 2).indicator (fun r => r ^ (-b - 1))
  have hbase : Integrable ((Ioi (2 : ℝ)).indicator (fun r => r ^ (-b))) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -b < -1)
      (by norm_num : (0 : ℝ) < 2)).integrable_indicator measurableSet_Ioi
  have hrad : Integrable (fun z : ℂ => f ‖z‖) := by
    rw [integrable_fun_norm_addHaar volume]
    apply hbase.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    by_cases h2 : 2 < r
    · simp only [f, mem_Ioi, indicator, h2, ↓reduceIte, finrank_real_complex,
        Nat.reduceSub, pow_one, smul_eq_mul]
      calc
        r ^ (-b) = r ^ (1 + (-b - 1)) := by congr 1; ring
        _ = r * r ^ (-b - 1) := by rw [Real.rpow_add hr, Real.rpow_one]
    · simp only [f, indicator, mem_Ioi, h2, ↓reduceIte, smul_zero]
  rw [← integrable_indicator_iff isClosed_closedBall.measurableSet.compl]
  apply hrad.congr
  filter_upwards [] with z
  simp only [f, indicator, mem_compl_iff, mem_closedBall_zero_iff, not_le, mem_Ioi]

private theorem integrable_unit_weighted_kernel {b : ℝ} (hb : 1 < b) (hb2 : b < 2) :
    Integrable (fun z : ℂ => ‖z‖ ^ (-b) / ‖z - 1‖) := by
  let k := fun z : ℂ => ‖z‖ ^ (-b) / ‖z - 1‖
  have hm : AEStronglyMeasurable k volume := by
    apply Measurable.aestronglyMeasurable
    dsimp only [k]
    fun_prop
  have hnear0 : IntegrableOn k (ball 0 (1 / 2)) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp) (C := 2) (α := b)
      (by simpa using hb2) _ hm
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hz0 := mem_ball_zero_iff.mp hz
    have hl := norm_le_norm_sub_add (1 : ℂ) z
    rw [norm_one, norm_sub_rev] at hl
    have hdist : (1 : ℝ) / 2 ≤ ‖z - 1‖ := by linarith
    have h := div_le_div_of_nonneg_left (Real.rpow_nonneg (norm_nonneg z) (-b))
      (by norm_num : (0 : ℝ) < 1 / 2) hdist
    calc
      ‖k z‖ = ‖z‖ ^ (-b) / ‖z - 1‖ :=
        abs_of_nonneg (by dsimp only [k]; positivity)
      _ ≤ ‖z‖ ^ (-b) / (1 / 2) := h
      _ = 2 * ‖z‖ ^ (-b) := by ring
  have hnear1 : IntegrableOn k (ball 1 (1 / 2)) := by
    have hi : IntegrableOn (fun z : ℂ => ‖(1 - z)⁻¹‖) (ball 1 (1 / 2)) := by
      have hclosed := (M65Branch.locallyIntegrable_cauchyKernel_sub (1 : ℂ)).integrableOn_isCompact
        (isCompact_closedBall (1 : ℂ) (1 / 2))
      exact (hclosed.mono_set ball_subset_closedBall).norm
    apply (hi.const_mul ((1 / 2 : ℝ) ^ (-b))).mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hz1 : ‖z - 1‖ < 1 / 2 := by simpa only [mem_ball, dist_eq_norm] using hz
    have hl := norm_le_norm_sub_add (1 : ℂ) z
    rw [norm_one, norm_sub_rev] at hl
    have hz0 : (1 : ℝ) / 2 ≤ ‖z‖ := by linarith
    have hp := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2)
      hz0 (by linarith : -b ≤ 0)
    have h := div_le_div_of_nonneg_right hp (norm_nonneg (z - 1))
    change |k z| ≤ _
    rw [abs_of_nonneg (show 0 ≤ k z by dsimp only [k]; positivity)]
    simpa only [k, norm_inv, norm_sub_rev (1 : ℂ) z, div_eq_mul_inv] using h
  let K := closedBall (0 : ℂ) 2 \ (ball 0 (1 / 2) ∪ ball 1 (1 / 2))
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 2).inter_right
    (isOpen_ball.union isOpen_ball).isClosed_compl
  have hmiddle : IntegrableOn k K := by
    apply ContinuousOn.integrableOn_compact hK
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hz.2 (Or.inl (mem_ball_self (by norm_num)))
    have hz1 : z - 1 ≠ 0 := by
      intro h
      have heq : z = 1 := sub_eq_zero.mp h
      exact hz.2 (Or.inr (heq ▸ mem_ball_self (by norm_num)))
    exact (((continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.mpr hz0))).div
      ((continuous_id.sub continuous_const).norm.continuousAt)
      (norm_ne_zero_iff.mpr hz1)).continuousWithinAt)
  have htail : IntegrableOn k (closedBall 0 2)ᶜ := by
    apply ((integrable_power_tail hb).const_mul 2).mono' hm.restrict
    filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet.compl] with z hz
    have hz2 : 2 < ‖z‖ := by simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hz
    have hz0 : 0 < ‖z‖ := by linarith
    have hl := norm_le_norm_sub_add z (1 : ℂ)
    rw [norm_one] at hl
    have hdist : ‖z‖ / 2 ≤ ‖z - 1‖ := by linarith
    have h := div_le_div_of_nonneg_left (Real.rpow_nonneg hz0.le (-b)) (by positivity) hdist
    have heq : ‖z‖ ^ (-b) / (‖z‖ / 2) = 2 * ‖z‖ ^ (-b - 1) := by
      rw [Real.rpow_sub hz0, Real.rpow_one]
      ring
    simpa only [k, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ‖z‖ ^ (-b) / ‖z - 1‖), heq] using h
  have hall := ((hnear0.union hnear1).union hmiddle).union htail
  have hcover : ((ball (0 : ℂ) (1 / 2) ∪ ball 1 (1 / 2)) ∪ K) ∪ (closedBall 0 2)ᶜ = univ := by
    dsimp only [K]
    ext z
    simp only [mem_union, mem_sdiff, mem_compl_iff, mem_univ, iff_true]
    tauto
  rwa [hcover, integrableOn_univ] at hall

private theorem complex_mul_change (f : ℂ → ℝ) {c : ℂ} (hc : c ≠ 0) :
    (Integrable (fun z => f (c * z)) ↔ Integrable f) ∧
      (∫ z, f (c * z)) = (‖c‖ ^ 2)⁻¹ * ∫ z, f z := by
  let u : ℂ := c / (‖c‖ : ℂ)
  have hr : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr,
      div_self hr.ne']
  have hu0 : u ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at hu
  let R : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { (LinearEquiv.smulOfNeZero ℂ ℂ u hu0).restrictScalars ℝ with
      norm_map' := by
        intro z
        change ‖u * z‖ = ‖z‖
        rw [norm_mul, hu, one_mul] }
  have heq (z : ℂ) : ‖c‖ • R z = c * z := by
    change (‖c‖ : ℂ) * ((c / (‖c‖ : ℂ)) * z) = c * z
    field_simp [ofReal_ne_zero.mpr hr.ne']
  have hR := R.measurePreserving
  have hEmb := R.toHomeomorph.measurableEmbedding
  constructor
  · have h := hR.integrable_comp_emb hEmb (g := fun z : ℂ => f (‖c‖ • z))
    simpa +instances only [Function.comp_def, heq] using!
      h.trans (integrable_comp_smul_iff volume f hr.ne')
  · calc
      _ = ∫ z : ℂ, f (‖c‖ • R z) := by simp only [heq]
      _ = ∫ z : ℂ, f (‖c‖ • z) := by
        simpa +instances only using! hR.integral_comp hEmb (fun z : ℂ => f (‖c‖ • z))
      _ = _ := by
        simpa only [finrank_real_complex, smul_eq_mul] using
          (Measure.integral_comp_smul_of_nonneg volume f ‖c‖ (hR := hr.le))

theorem weighted_inverse_kernel {b : ℝ} (hb : 1 < b) (hb2 : b < 2) :
    ∃ C > 0, ∀ x w : ℂ, x ≠ w →
      Integrable (fun z : ℂ => ‖x - z‖ ^ (-b) / ‖z - w‖) ∧
      (∫ z : ℂ, ‖x - z‖ ^ (-b) / ‖z - w‖) ≤ C * ‖w - x‖ ^ (1 - b) := by
  let k := fun z : ℂ => ‖z‖ ^ (-b) / ‖z - 1‖
  let I := ∫ z, k z
  have hk : Integrable k := integrable_unit_weighted_kernel hb hb2
  have hI : 0 ≤ I := integral_nonneg (fun _ => by dsimp only [k]; positivity)
  refine ⟨I + 1, by positivity, ?_⟩
  intro x w hxw
  let c := w - x
  let f := fun z : ℂ => ‖x - z‖ ^ (-b) / ‖z - w‖
  have hc : c ≠ 0 := sub_ne_zero.mpr hxw.symm
  have hr : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hpoint (z : ℂ) : f (x + c * z) = (‖c‖ ^ (-b) / ‖c‖) * k z := by
    have hl : x - (x + c * z) = -(c * z) := by ring
    have hh : x + c * z - w = c * (z - 1) := by dsimp only [c]; ring
    dsimp only [f, k]
    rw [hl, hh, norm_neg, norm_mul, norm_mul, Real.mul_rpow (norm_nonneg c) (norm_nonneg z)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have htranslated : Integrable (fun z => f (x + z)) := by
    apply (complex_mul_change (fun z => f (x + z)) hc).1.mp
    simpa only [hpoint] using hk.const_mul (‖c‖ ^ (-b) / ‖c‖)
  have hf : Integrable f := by
    simpa only [add_neg_cancel_left] using htranslated.comp_add_left (-x)
  refine ⟨hf, ?_⟩
  have hchange : (∫ z, f (x + c * z)) = (‖c‖ ^ 2)⁻¹ * ∫ z, f z := by
    rw [(complex_mul_change (fun z => f (x + z)) hc).2, integral_add_left_eq_self f x]
  have hscale : ‖c‖ ^ 2 * (‖c‖ ^ (-b) / ‖c‖) = ‖c‖ ^ (1 - b) := by
    calc
      _ = ‖c‖ * ‖c‖ ^ (-b) := by field_simp
      _ = ‖c‖ ^ (1 + (-b)) := by rw [Real.rpow_add hr, Real.rpow_one]
      _ = _ := by rw [sub_eq_add_neg]
  have hactual : (∫ z, f z) = ‖c‖ ^ (1 - b) * I := by
    calc
      _ = ‖c‖ ^ 2 * ((‖c‖ ^ 2)⁻¹ * ∫ z, f z) := by field_simp
      _ = ‖c‖ ^ 2 * ∫ z, f (x + c * z) := by rw [hchange]
      _ = ‖c‖ ^ 2 * ((‖c‖ ^ (-b) / ‖c‖) * I) := by
        simp_rw [hpoint, integral_const_mul]
        rfl
      _ = _ := by rw [← mul_assoc, hscale]
  change (∫ z, f z) ≤ (I + 1) * ‖c‖ ^ (1 - b)
  rw [hactual, mul_comm]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hr.le _)

end PoincareConjecture.M65Boundary
