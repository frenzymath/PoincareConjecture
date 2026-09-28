import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveOscillation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import Mathlib.MeasureTheory.Integral.Average









set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64

local notation "b" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)




theorem rectangle_exists_energy_controlled_normalization
    (F : LoopPlane → ℝ) (hF : ContDiff ℝ 1 F)
    {width height : ℝ} (hw : 0 < width) (hh : 0 < height) :
    ∃ c : ℝ,
      (∫ y in Icc (0 : ℝ) height, ∫ x in Icc (0 : ℝ) width,
        (F (annulusPoint x y) - c) ^ 2) ≤
      8 * width ^ 2 * (∫ y in Icc (0 : ℝ) height, ∫ x in Icc (0 : ℝ) width,
        (fderiv ℝ F (annulusPoint x y) (b 0)) ^ 2) +
      8 * height ^ 2 * (∫ x in Icc (0 : ℝ) width, ∫ y in Icc (0 : ℝ) height,
        (fderiv ℝ F (annulusPoint x y) (b 1)) ^ 2) := by
  let D := fun (i : Fin 2) (p : LoopPlane) => fderiv ℝ F p (b i)
  have hD (i : Fin 2) : Continuous (D i) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  let row := fun y => ∫ x in Icc (0 : ℝ) width, D 0 (annulusPoint x y) ^ 2
  let col := fun x => ∫ y in Icc (0 : ℝ) height, D 1 (annulusPoint x y) ^ 2
  have hrow : Continuous row := by
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ((hD 0).comp (by unfold annulusPoint; fun_prop)).pow 2
  have hcol : Continuous col := by
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ((hD 1).comp (by unfold annulusPoint; fun_prop)).pow 2
  have hvol : volume (Icc (0 : ℝ) width) ≠ 0 := by
    rw [Real.volume_Icc, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hw).ne'
  obtain ⟨s, hs, havg⟩ := exists_le_setAverage hvol isCompact_Icc.measure_ne_top
    hcol.integrableOn_Icc
  rw [setAverage_eq, Real.volume_real_Icc_of_le hw.le, sub_zero, smul_eq_mul] at havg
  have hanchor : width * col s ≤ ∫ x in Icc (0 : ℝ) width, col x := by
    have h := mul_le_mul_of_nonneg_left havg hw.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul] using h
  let c := F (annulusPoint s 0)
  have hpoint (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) width) (hy : y ∈ Icc (0 : ℝ) height) :
      (F (annulusPoint x y) - c) ^ 2 ≤ 8 * width * row y + 8 * height * col s := by
    have hhor := m64Curve_oscillation_sq_le (fun u => F (annulusPoint u y))
      (fun u => D 0 (annulusPoint u y))
      ((hD 0).comp (by unfold annulusPoint; fun_prop))
      (fun u => (hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt u
        (m64AnnulusPoint_horizontal_hasDerivAt y u)) hx hs
    have hver := m64Curve_oscillation_sq_le (fun v => F (annulusPoint s v))
      (fun v => D 1 (annulusPoint s v))
      ((hD 1).comp (by unfold annulusPoint; fun_prop))
      (fun v => (hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt v
        (m64AnnulusPoint_vertical_hasDerivAt s v)) hy ⟨le_rfl, hh.le⟩
    simp only [Real.norm_eq_abs, sq_abs] at hhor hver
    change (F (annulusPoint x y) - F (annulusPoint s y)) ^ 2 ≤
      4 * width * row y at hhor
    change (F (annulusPoint s y) - c) ^ 2 ≤ 4 * height * col s at hver
    nlinarith [sq_nonneg (F (annulusPoint x y) - F (annulusPoint s y) -
      (F (annulusPoint s y) - c))]
  let H := fun y => ∫ x in Icc (0 : ℝ) width, (F (annulusPoint x y) - c) ^ 2
  have hH : Continuous H := by
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ((hF.continuous.comp (by unfold annulusPoint; fun_prop)).sub continuous_const).pow 2
  have hinner (y : ℝ) (hy : y ∈ Icc (0 : ℝ) height) :
      H y ≤ 8 * width ^ 2 * row y + 8 * width * height * col s := by
    have hc : Continuous (fun x => (F (annulusPoint x y) - c) ^ 2) :=
      ((hF.continuous.comp (by unfold annulusPoint; fun_prop)).sub continuous_const).pow 2
    have h := setIntegral_mono_on (μ := volume) hc.integrableOn_Icc
      (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc
      (fun x hx => hpoint x y hx hy)
    simp only [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hw.le,
      sub_zero] at h
    exact h.trans_eq (by ring)
  have houter := setIntegral_mono_on (μ := volume) hH.integrableOn_Icc
    (((hrow.const_mul (8 * width ^ 2)).add continuous_const).integrableOn_Icc)
    measurableSet_Icc hinner
  have heq : (∫ y in Icc (0 : ℝ) height,
      8 * width ^ 2 * row y + 8 * width * height * col s) =
      8 * width ^ 2 * (∫ y in Icc (0 : ℝ) height, row y) +
        8 * height ^ 2 * (width * col s) := by
    rw [integral_add (hrow.integrableOn_Icc.const_mul _)
      (integrableOn_const isCompact_Icc.measure_ne_top), integral_const_mul,
      setIntegral_const, Real.volume_real_Icc_of_le hh.le]
    simp only [sub_zero, smul_eq_mul]
    ring
  refine ⟨c, ?_⟩
  change (∫ y in Icc (0 : ℝ) height, H y) ≤
    8 * width ^ 2 * (∫ y in Icc (0 : ℝ) height, row y) +
      8 * height ^ 2 * (∫ x in Icc (0 : ℝ) width, col x)
  change (∫ y in Icc (0 : ℝ) height, H y) ≤
    ∫ y in Icc (0 : ℝ) height,
      8 * width ^ 2 * row y + 8 * width * height * col s at houter
  rw [heq] at houter
  exact houter.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hanchor (by positivity : 0 ≤ 8 * height ^ 2)))




theorem annulus_exists_energy_controlled_normalization
    (F : LoopPlane → ℝ) (hF : ContDiff ℝ 1 F) :
    ∃ c : ℝ,
      (∫ p in interior m64AnnulusDomain, (F p - c) ^ 2) ≤
      8 * curvePeriod ^ 2 *
        (∫ p in interior m64AnnulusDomain, (fderiv ℝ F p (b 0)) ^ 2) +
      8 * (∫ p in interior m64AnnulusDomain, (fderiv ℝ F p (b 1)) ^ 2) := by
  obtain ⟨c, hc⟩ := rectangle_exists_energy_controlled_normalization F hF (width := curvePeriod)
    (by unfold curvePeriod; positivity) (by norm_num : (0 : ℝ) < 1)
  have hI (f : LoopPlane → ℝ) (hf : Continuous f) :
      IntegrableOn f (interior m64AnnulusDomain) volume :=
    hf.continuousOn.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  refine ⟨c, ?_⟩
  rw [m64AnnulusInteriorIntegral_eq_iterated_swap_integrable (fun p => (F p - c) ^ 2)
    (hI _ ((hF.continuous.sub continuous_const).pow 2)),
    m64AnnulusInteriorIntegral_eq_iterated_swap_integrable (fun p => (fderiv ℝ F p (b 0)) ^ 2)
      (hI _ (((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2)),
    m64AnnulusInteriorIntegral_eq_iterated_integrable (fun p => (fderiv ℝ F p (b 1)) ^ 2)
      (hI _ (((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2))]
  simpa only [one_pow, mul_one] using hc




theorem translated_rectangle_exists_energy_controlled_normalization
    (F : LoopPlane → ℝ) (hF : ContDiff ℝ 1 F)
    {x₀ y₀ width height : ℝ} (hw : 0 < width) (hh : 0 < height) :
    ∃ c : ℝ,
      (∫ y in Icc (0 : ℝ) height, ∫ x in Icc (0 : ℝ) width,
        (F (annulusPoint (x₀ + x) (y₀ + y)) - c) ^ 2) ≤
      8 * width ^ 2 * (∫ y in Icc (0 : ℝ) height, ∫ x in Icc (0 : ℝ) width,
        (fderiv ℝ F (annulusPoint (x₀ + x) (y₀ + y)) (b 0)) ^ 2) +
      8 * height ^ 2 * (∫ x in Icc (0 : ℝ) width, ∫ y in Icc (0 : ℝ) height,
        (fderiv ℝ F (annulusPoint (x₀ + x) (y₀ + y)) (b 1)) ^ 2) := by
  let T : LoopPlane := annulusPoint x₀ y₀
  let G : LoopPlane → ℝ := fun p => F (T + p)
  have hG : ContDiff ℝ 1 G := by
    exact hF.comp (contDiff_const.add contDiff_id)
  obtain ⟨c, hc⟩ := rectangle_exists_energy_controlled_normalization G hG hw hh
  refine ⟨c, ?_⟩
  have hpoint (x y : ℝ) : T + annulusPoint x y =
      annulusPoint (x₀ + x) (y₀ + y) := by
    ext i
    fin_cases i <;> simp [T, annulusPoint]
  have hder (p : LoopPlane) (i : Fin 2) :
      fderiv ℝ G p (b i) = fderiv ℝ F (T + p) (b i) := by
    simpa only [G] using congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (b i))
      (fderiv_comp_add_left (f := F) T)
  simpa only [G, Function.comp_apply, hpoint, hder] using hc

end PoincareConjecture.M64
