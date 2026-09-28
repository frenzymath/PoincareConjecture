import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity










set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff Interval

namespace Real

private theorem surjective_of_deriv_lower_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : Differentiable ℝ f) (hC : 0 < C) (hd : ∀ x, C ≤ deriv f x) :
    Function.Surjective f := by
  apply hf.continuous.surjective
  · refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (max 0 ((b - f 0) / C))] with x hx
    have hx0 : 0 ≤ x := (le_max_left _ _).trans hx
    have hb : b - f 0 ≤ x * C := (div_le_iff₀ hC).mp ((le_max_right _ _).trans hx)
    have hg := mul_sub_le_image_sub_of_le_deriv hf hd hx0
    nlinarith
  · refine tendsto_atBot.2 fun b => ?_
    filter_upwards [eventually_le_atBot (min 0 ((b - f 0) / C))] with x hx
    have hx0 : x ≤ 0 := hx.trans (min_le_left _ _)
    have hb : x * C ≤ b - f 0 := (le_div_iff₀ hC).mp (hx.trans (min_le_right _ _))
    have hg := mul_sub_le_image_sub_of_le_deriv hf hd hx0
    nlinarith




theorem exists_smooth_orderIso_compression {c b A : ℝ} (hcb : c < b) (hbA : b < A) :
    ∃ e : ℝ ≃o ℝ, ContDiff ℝ ∞ (e : ℝ → ℝ) ∧
      ContDiff ℝ ∞ (e.symm : ℝ → ℝ) ∧ e A = b ∧
      (∀ x ≤ c, e x = x) ∧ ∀ x, 0 < deriv (e : ℝ → ℝ) x ∧
        deriv (e : ℝ → ℝ) x ≤ 1 := by
  let d := (c + b) / 2
  have hcd : c < d := by dsimp [d]; linarith
  have hdb : d < b := by dsimp [d]; linarith
  have hdA : d < A := hdb.trans hbA
  have hcA : c < A := hcb.trans hbA
  let χ : ℝ → ℝ := fun x => 1 - smoothTransition ((x - c) / (d - c))
  have hχ : ContDiff ℝ ∞ χ :=
    contDiff_const.sub ((smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      ((contDiff_id.sub contDiff_const).div_const (d - c)))
  have hχ0 (x : ℝ) : 0 ≤ χ x := sub_nonneg.mpr (smoothTransition.le_one _)
  have hχ1 (x : ℝ) : χ x ≤ 1 := sub_le_self _ (smoothTransition.nonneg _)
  have hχleft {x : ℝ} (hx : x ≤ c) : χ x = 1 := by
    dsimp [χ]
    rw [smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hcd).le)]
    ring
  have hχright {x : ℝ} (hx : d ≤ x) : χ x = 0 := by
    dsimp [χ]
    rw [smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hcd)).mpr (by linarith))]
    ring
  let I : ℝ := ∫ x in c..A, χ x
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg_of_forall hcA.le hχ0
  have hId : I ≤ d - c := by
    have hz : (∫ x in d..A, χ x) = 0 := by
      calc
        (∫ x in d..A, χ x) = ∫ _ in d..A, (0 : ℝ) :=
          intervalIntegral.integral_congr fun x hx =>
            hχright ((uIcc_of_le hdA.le ▸ hx).1)
        _ = 0 := by simp
    have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hcd.le
      (hχ.continuous.intervalIntegrable c d) (continuous_const.intervalIntegrable c d)
      (fun x _ => hχ1 x)
    have hs := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hχ.continuous.intervalIntegrable c d) (hχ.continuous.intervalIntegrable d A)
    dsimp [I]
    rw [← hs, hz, add_zero]
    simpa using hm
  have hIb : I < b - c := by linarith
  have hden : 0 < A - c - I := by linarith
  let l := (b - c - I) / (A - c - I)
  have hl : 0 < l := div_pos (by linarith) hden
  have hl1 : l < 1 := (div_lt_one hden).mpr (by linarith)
  have hleq : l * (A - c - I) = b - c - I := div_mul_cancel₀ _ hden.ne'
  let P : ℝ → ℝ := fun x => ∫ y in c..x, χ y
  have hPderiv (x : ℝ) : HasDerivAt P (χ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hχ.continuous.intervalIntegrable c x)
      hχ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hχ.continuous.continuousAt
  have hP : ContDiff ℝ ∞ P := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (hPderiv x).differentiableAt, ?_⟩
    have heq : deriv P = χ := funext fun x => (hPderiv x).deriv
    rw [heq]
    exact hχ
  let f : ℝ → ℝ := fun x => c + (l * (x - c) + (1 - l) * P x)
  have hf : ContDiff ℝ ∞ f :=
    contDiff_const.add ((contDiff_const.mul (contDiff_id.sub contDiff_const)).add
      (contDiff_const.mul hP))
  have hfderiv (x : ℝ) : HasDerivAt f (l + (1 - l) * χ x) x := by
    convert! ((((hasDerivAt_id x).sub_const c).const_mul l).add
      ((hPderiv x).const_mul (1 - l))).const_add c using 1
    simp only [mul_one]
  have hd0 (x : ℝ) : l ≤ deriv f x := by
    rw [(hfderiv x).deriv]
    exact le_add_of_nonneg_right (mul_nonneg (sub_pos.mpr hl1).le (hχ0 x))
  have hd1 (x : ℝ) : deriv f x ≤ 1 := by
    rw [(hfderiv x).deriv]
    nlinarith [mul_le_mul_of_nonneg_left (hχ1 x) (sub_pos.mpr hl1).le]
  have hm : StrictMono f := strictMono_of_deriv_pos fun x => hl.trans_le (hd0 x)
  have hs : Function.Surjective f := surjective_of_deriv_lower_bound
    (fun x => (hfderiv x).differentiableAt) hl hd0
  let e : ℝ ≃o ℝ := hm.orderIsoOfSurjective f hs
  have he : (e : ℝ → ℝ) = f := rfl
  refine ⟨e, he ▸ hf, ?_, ?_, ?_, ?_⟩
  · exact e.toHomeomorph.contDiff_symm_deriv (fun x => (hl.trans_le (hd0 x)).ne')
      (fun x => (hfderiv x).congr_deriv (hfderiv x).deriv.symm) (he ▸ hf)
  · change f A = b
    change c + (l * (A - c) + (1 - l) * I) = b
    nlinarith [hleq]
  · intro x hx
    have hPx : P x = x - c := by
      calc
        P x = ∫ _ in c..x, (1 : ℝ) := intervalIntegral.integral_congr fun y hy =>
          hχleft ((uIcc_of_ge hx ▸ hy).2)
        _ = x - c := by simp
    change f x = x
    dsimp [f]
    rw [hPx]
    ring
  · intro x
    rw [he]
    exact ⟨hl.trans_le (hd0 x), hd1 x⟩

end Real
