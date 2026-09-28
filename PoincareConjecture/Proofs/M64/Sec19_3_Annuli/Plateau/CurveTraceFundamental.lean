import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveL2Trace
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]



theorem m64Curve_trace_fundamental_of_strong_approximation
    (w d : ℕ → ℝ → E) (hd : ∀ j, Continuous (d j))
    (hw : ∀ j t, HasDerivAt (w j) (d j t) t) {T : ℝ} (hT : 0 < T)
    (v W : ℝ → E) (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hder : Tendsto (fun j => ∫ t in Icc (0 : ℝ) T, ‖d j t - v t‖ ^ 2) atTop (𝓝 0))
    (hW : TendstoUniformlyOn w W atTop (Icc (0 : ℝ) T)) :
    ∀ x ∈ Icc (0 : ℝ) T, W x - W 0 = ∫ t in (0 : ℝ)..x, v t := by
  let mu := volume.restrict (Icc (0 : ℝ) T)
  have hdL (j : ℕ) : MemLp (d j) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm (hd j).aestronglyMeasurable).mpr
    exact ((hd j).norm.pow 2).integrableOn_Icc
  have hn (j : ℕ) : ‖(hdL j).toLp (d j) - hv.toLp v‖ ^ 2 =
      ∫ t in Icc (0 : ℝ) T, ‖d j t - v t‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hdL j).toLp (d j)) (hv.toLp v),
      (hdL j).coeFn_toLp, hv.coeFn_toLp] with t ht hdt hvt
    simp only [ht, Pi.sub_apply, hdt, hvt]
  have hL : Tendsto (fun j => (hdL j).toLp (d j)) atTop (𝓝 (hv.toLp v)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs : Tendsto (fun j => ‖(hdL j).toLp (d j) - hv.toLp v‖ ^ 2) atTop (𝓝 0) := by
      simpa only [hn] using hder
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt
  intro x hx
  let phi := (Ioc (0 : ℝ) x).indicator (fun _ : ℝ => (1 : ℝ))
  have hp : MemLp phi 2 mu :=
    (memLp_const (1 : ℝ)).indicator measurableSet_Ioc
  have hsub : Ioc (0 : ℝ) x ⊆ Icc (0 : ℝ) T :=
    fun t ht => ⟨ht.1.le, ht.2.trans hx.2⟩
  have heq (u : ℝ → E) (hu : MemLp u 2 mu) :
      testIntegral phi hp (hu.toLp u) = ∫ t in (0 : ℝ)..x, u t := by
    rw [testIntegral_toLp]
    have hi : (fun t => phi t • u t) = (Ioc (0 : ℝ) x).indicator u := by
      funext t
      by_cases ht : t ∈ Ioc (0 : ℝ) x <;> simp [phi, ht]
    rw [hi, integral_indicator measurableSet_Ioc]
    change (∫ t, u t ∂(volume.restrict (Icc (0 : ℝ) T)).restrict (Ioc (0 : ℝ) x)) = _
    rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub,
      intervalIntegral.integral_of_le hx.1]
  have hint := ((testIntegral phi hp).continuous.tendsto (hv.toLp v)).comp hL
  simp only [Function.comp_def, heq] at hint
  have hFTC (j : ℕ) : (∫ t in (0 : ℝ)..x, d j t) = w j x - w j 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hw j t)
      ((hd j).intervalIntegrable 0 x)
  simp only [hFTC] at hint
  exact tendsto_nhds_unique ((hW.tendsto_at hx).sub (hW.tendsto_at ⟨le_rfl, hT.le⟩)) hint

omit [CompleteSpace E] in


theorem m64Curve_trace_oscillation_sq_le
    (W v : ℝ → E) {T : ℝ} (_hT : 0 < T)
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hFTC : ∀ x ∈ Icc (0 : ℝ) T, W x - W 0 = ∫ t in (0 : ℝ)..x, v t)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) T) (hy : y ∈ Icc (0 : ℝ) T) :
    ‖W x - W y‖ ^ 2 ≤ 4 * T * ∫ t in Icc (0 : ℝ) T, ‖v t‖ ^ 2 := by
  let Q := ∫ t in Icc (0 : ℝ) T, ‖v t‖ ^ 2
  have hQ : 0 ≤ Q := integral_nonneg (fun t => sq_nonneg _)
  have hi : IntegrableOn (fun t => ‖v t‖ ^ 2) (Icc (0 : ℝ) T) volume :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hanchor (z : ℝ) (hz : z ∈ Icc (0 : ℝ) T) : ‖W z - W 0‖ ^ 2 ≤ T * Q := by
    have hvz : IntervalIntegrable v volume 0 z := by
      apply IntegrableOn.intervalIntegrable
      rw [uIcc_of_le hz.1]
      exact (show IntegrableOn v (Icc (0 : ℝ) T) volume from
        hv.integrable (by norm_num)).mono_set (Icc_subset_Icc le_rfl hz.2)
    have hsz : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 z := by
      apply IntegrableOn.intervalIntegrable
      rw [uIcc_of_le hz.1]
      exact hi.mono_set (Icc_subset_Icc le_rfl hz.2)
    have hnorm := intervalIntegral.norm_integral_le_integral_norm (f := v) (μ := volume) hz.1
    have hnorm0 : 0 ≤ ∫ t in (0 : ℝ)..z, ‖v t‖ :=
      intervalIntegral.integral_nonneg hz.1 (fun _ _ => norm_nonneg _)
    have hCS := SpectralHeatNative.integral_sq_le_time_mul_integral_sq hz.1 hvz.norm hsz
    have hsmall : (∫ t in (0 : ℝ)..z, ‖v t‖ ^ 2) ≤ Q := by
      rw [intervalIntegral.integral_of_le hz.1]
      exact setIntegral_mono_set hi (Eventually.of_forall (fun t => sq_nonneg _))
        (Eventually.of_forall (fun t ht => ⟨ht.1.le, ht.2.trans hz.2⟩))
    rw [hFTC z hz]
    exact ((sq_le_sq₀ (norm_nonneg _) hnorm0).mpr hnorm).trans
      (hCS.trans ((mul_le_mul_of_nonneg_left hsmall hz.1).trans
        (mul_le_mul_of_nonneg_right hz.2 hQ)))
  have htriangle : ‖W x - W y‖ ≤ ‖W x - W 0‖ + ‖W y - W 0‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (W x - W 0) (W y - W 0)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htriangle
  have hx0 := hanchor x hx
  have hy0 := hanchor y hy
  nlinarith [sq_nonneg (‖W x - W 0‖ - ‖W y - W 0‖)]

end PoincareConjecture
