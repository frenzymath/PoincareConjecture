import PoincareConjecture.Proofs.Horizon.Analysis.Heat.RealKernel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper









set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Poincare.Analysis.Heat

theorem integrable_standardGaussian_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun z ↦ gaussianPDFReal 0 1 z * f z) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  simp

theorem integrable_id_mul_of_lipschitz_standardGaussian {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) :
    Integrable (fun z ↦ z * f z) (gaussianReal 0 1) := by
  have hsq : Integrable (fun z : ℝ ↦ z ^ 2) (gaussianReal 0 1) := by
    simpa only [id_eq, Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow (by norm_num)
  apply ((integrable_abs_standardGaussian.mul_const |f 0|).add
    (hsq.const_mul (L : ℝ))).mono' (continuous_id.mul hf.continuous).aestronglyMeasurable
  filter_upwards [] with z
  have h := hf.dist_le_mul z 0
  simp only [Real.dist_eq, sub_zero] at h
  have htri := abs_add_le (f 0) (f z - f 0)
  simp only [add_sub_cancel] at htri
  simp only [Pi.add_apply, Real.norm_eq_abs, Pi.mul_apply, id_eq, abs_mul]
  calc
    |z| * |f z| ≤ |z| * (|f 0| + (L : ℝ) * |z|) :=
      mul_le_mul_of_nonneg_left (htri.trans (add_le_add_right h _)) (abs_nonneg z)
    _ = |z| * |f 0| + (L : ℝ) * z ^ 2 := by
      rw [mul_add, mul_left_comm |z| (L : ℝ), ← sq, sq_abs]

theorem integrable_deriv_of_lipschitz_standardGaussian {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) :
    Integrable (deriv f) (gaussianReal 0 1) := by
  exact (integrable_const (L : ℝ)).mono' (measurable_deriv f).aestronglyMeasurable
    (ae_of_all _ fun _ ↦ norm_deriv_le_of_lipschitz hf)



theorem integral_deriv_standardGaussian {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f) :
    (∫ z, deriv f z ∂gaussianReal 0 1) =
      ∫ z, z * f z ∂gaussianReal 0 1 := by
  have hk : realHeatKernel (1 / 2) = gaussianPDFReal 0 1 := by
    funext z
    rw [realHeatKernel_eq_gaussianPDFReal (by norm_num : 0 ≤ (1 : ℝ) / 2)]
    congr 1
    apply Subtype.ext
    norm_num
  have hK (z : ℝ) : HasDerivAt (gaussianPDFReal 0 1)
      (-z * gaussianPDFReal 0 1 z) z := by
    have h := hasDerivAt_realHeatKernel_space (by norm_num : 0 < (1 : ℝ) / 2) z
    norm_num [hk] at h ⊢
    exact h
  have hi : Integrable (fun z ↦ gaussianPDFReal 0 1 z * f z) := by
    apply integrable_standardGaussian_iff.mp
    simpa using
      integrable_gaussianAverage hf (1 / 2) 0
  have hiz := integrable_standardGaussian_iff.mp
    (integrable_id_mul_of_lipschitz_standardGaussian hf)
  have hid := integrable_standardGaussian_iff.mp
    (integrable_deriv_of_lipschitz_standardGaussian hf)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := gaussianPDFReal 0 1) (v := f)
    (u' := fun z ↦ -z * gaussianPDFReal 0 1 z) (v' := deriv f)
    (fun z _ ↦ hK z) (fun z _ ↦ (hdf z).hasDerivAt) hid ?_ hi
  · simp_rw [integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) one_ne_zero,
      smul_eq_mul]
    rw [h]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  · convert! hiz.neg using 1
    ext z
    simp only [Pi.neg_apply, Pi.mul_apply]
    ring

theorem lipschitzWith_gaussianIntegrand {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (t x : ℝ) :
    LipschitzWith (L * Real.nnabs (Real.sqrt (2 * t)))
      (fun z ↦ f (x + Real.sqrt (2 * t) * z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := hf.dist_le_mul (x + Real.sqrt (2 * t) * z)
    (x + Real.sqrt (2 * t) * w)
  simpa only [NNReal.coe_mul, Real.coe_nnabs, Real.dist_eq,
    add_sub_add_left_eq_sub, ← mul_sub, abs_mul, mul_assoc] using h

theorem gaussianAverage_deriv_eq {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    gaussianAverage (deriv f) t x =
      ∫ z, (z / Real.sqrt (2 * t)) * f (x + Real.sqrt (2 * t) * z)
        ∂gaussianReal 0 1 := by
  have ha : Real.sqrt (2 * t) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hd (z : ℝ) : HasDerivAt (fun w ↦ f (x + Real.sqrt (2 * t) * w))
      (deriv f (x + Real.sqrt (2 * t) * z) * Real.sqrt (2 * t)) z := by
    simpa only [Function.comp_def, id_eq, mul_one] using!
      (hdf _).hasDerivAt.comp z (((hasDerivAt_id z).const_mul _).const_add x)
  have h := integral_deriv_standardGaussian (lipschitzWith_gaussianIntegrand hf t x)
    (fun z ↦ (hd z).differentiableAt)
  simp_rw [(hd _).deriv] at h
  rw [integral_mul_const] at h
  apply (eq_div_iff ha).mpr at h
  unfold gaussianAverage
  rw [h, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

theorem hasDerivAt_gaussianAverage_twice {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (deriv (gaussianAverage f t))
      (∫ z, (z / Real.sqrt (2 * t)) * deriv f (x + Real.sqrt (2 * t) * z)
        ∂gaussianReal 0 1) x := by
  have heq : deriv (gaussianAverage f t) = fun a ↦
      ∫ z, (z / Real.sqrt (2 * t)) * f (a + Real.sqrt (2 * t) * z)
        ∂gaussianReal 0 1 := by
    funext a
    rw [(hasDerivAt_gaussianAverage hf hdf t a).deriv,
      gaussianAverage_deriv_eq hf hdf ht]
  rw [heq]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := Set.univ)
    (bound := fun z : ℝ ↦ (|z| / Real.sqrt (2 * t)) * (L : ℝ))
    (F := fun a z : ℝ ↦ (z / Real.sqrt (2 * t)) * f (a + Real.sqrt (2 * t) * z))
    (F' := fun a z : ℝ ↦ (z / Real.sqrt (2 * t)) * deriv f (a + Real.sqrt (2 * t) * z))
    (x₀ := x) univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact h.2
  · exact Eventually.of_forall fun a ↦
      ((continuous_id.div_const _).mul (hf.continuous.comp (by fun_prop))).aestronglyMeasurable
  · convert! (integrable_id_mul_of_lipschitz_standardGaussian
      (lipschitzWith_gaussianIntegrand hf t x)).div_const (Real.sqrt (2 * t)) using 1
    ext z
    ring
  · exact ((measurable_id.div_const _).mul
      ((measurable_deriv f).comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [] with z
    intro a _
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hf) (by positivity)
  · exact (integrable_abs_standardGaussian.div_const _).mul_const _
  · filter_upwards [] with z
    intro a _
    have hd := (hdf _).hasDerivAt.comp a
      ((hasDerivAt_id a).add_const (Real.sqrt (2 * t) * z))
    simpa only [Function.comp_def, id_eq, mul_one] using!
      hd.const_mul (z / Real.sqrt (2 * t))

theorem hasDerivAt_gaussianAverage_time {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s ↦ gaussianAverage f s x)
      (∫ z, deriv f (x + Real.sqrt (2 * t) * z) *
        (z / Real.sqrt (2 * t)) ∂gaussianReal 0 1) t := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := Set.Ioi (t / 2))
    (bound := fun z : ℝ ↦ (L : ℝ) * (|z| / Real.sqrt t))
    (F := fun s z : ℝ ↦ f (x + Real.sqrt (2 * s) * z))
    (F' := fun s z : ℝ ↦ deriv f (x + Real.sqrt (2 * s) * z) *
      (z / Real.sqrt (2 * s)))
    (x₀ := t) (Ioi_mem_nhds (by linarith)) ?_
    (integrable_gaussianAverage hf t x) ?_ ?_ ?_ ?_
  · exact h.2
  · exact Eventually.of_forall fun s ↦
      (integrable_gaussianAverage hf s x).aestronglyMeasurable
  · exact (((measurable_deriv f).comp (by fun_prop)).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with z
    intro s hs
    have hs0 : 0 < s := by change t / 2 < s at hs; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul
    · exact norm_deriv_le_of_lipschitz hf
    · apply div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.mpr ht)
      apply Real.sqrt_le_sqrt
      change t / 2 < s at hs
      linarith
    · positivity
    · positivity
  · exact (integrable_abs_standardGaussian.div_const _).const_mul _
  · filter_upwards [] with z
    intro s hs
    have hs0 : 0 < s := by change t / 2 < s at hs; linarith
    have hd := (((hasDerivAt_id s).const_mul 2).sqrt
      (by positivity : 2 * s ≠ 0)).mul_const z
    have hc := (hdf (x + Real.sqrt (2 * s) * z)).hasDerivAt.comp s
      (hd.const_add x)
    convert! hc using 1
    simp only [id_eq, mul_one]
    field_simp

theorem gaussianAverage_heatEquation {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s ↦ gaussianAverage f s x)
      (deriv (deriv (gaussianAverage f t)) x) t := by
  rw [(hasDerivAt_gaussianAverage_twice hf hdf ht x).deriv]
  convert! hasDerivAt_gaussianAverage_time hf hdf ht x using 1
  apply integral_congr_ae
  filter_upwards [] with z
  ring

theorem realHeatEvolution_estimates {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f) :
    TendstoUniformly (gaussianAverage f) f (𝓝[>] (0 : ℝ)) ∧
    ∀ t : ℝ, 0 < t →
      Differentiable ℝ (gaussianAverage f t) ∧
      Differentiable ℝ (deriv (gaussianAverage f t)) ∧
      ∀ x : ℝ,
        HasDerivAt (fun s ↦ gaussianAverage f s x)
          (deriv (deriv (gaussianAverage f t)) x) t ∧
        |gaussianAverage f t x - f x| ≤ (L : ℝ) * Real.sqrt (2 * t) ∧
        |deriv (gaussianAverage f t) x| ≤ (L : ℝ) := by
  refine ⟨tendstoUniformly_gaussianAverage hf, fun t ht ↦ ⟨?_, ?_, ?_⟩⟩
  · exact fun x ↦ (hasDerivAt_gaussianAverage hf hdf t x).differentiableAt
  · exact fun x ↦ (hasDerivAt_gaussianAverage_twice hf hdf ht x).differentiableAt
  · exact fun x ↦ ⟨gaussianAverage_heatEquation hf hdf ht x,
      abs_gaussianAverage_sub_le hf t x, abs_deriv_gaussianAverage_le hf t x⟩

theorem abs_deriv_gaussianAverage_twice_le {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |deriv (deriv (gaussianAverage f t)) x| ≤ (L : ℝ) / Real.sqrt (2 * t) := by
  rw [(hasDerivAt_gaussianAverage_twice hf hdf ht x).deriv]
  have hb : ∀ᵐ z ∂gaussianReal 0 1,
      ‖(z / Real.sqrt (2 * t)) * deriv f (x + Real.sqrt (2 * t) * z)‖ ≤
        ((L : ℝ) / Real.sqrt (2 * t)) * |z| := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (|z| / Real.sqrt (2 * t)) * (L : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hf) (by positivity)
      _ = _ := by ring
  have h := norm_integral_le_of_norm_le
    (integrable_abs_standardGaussian.const_mul ((L : ℝ) / Real.sqrt (2 * t))) hb
  rw [integral_const_mul] at h
  exact h.trans (by
    simpa using mul_le_mul_of_nonneg_left integral_abs_standardGaussian_le_one
      (by positivity : 0 ≤ (L : ℝ) / Real.sqrt (2 * t)))

theorem lipschitzWith_deriv_gaussianAverage {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f)
    {t : ℝ} (ht : 0 < t) :
    LipschitzWith (L / Real.nnabs (Real.sqrt (2 * t))) (deriv (gaussianAverage f t)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x ↦ (hasDerivAt_gaussianAverage_twice hf hdf ht x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_div, Real.coe_nnabs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using abs_deriv_gaussianAverage_twice_le hf hdf ht x

end Poincare.Analysis.Heat
