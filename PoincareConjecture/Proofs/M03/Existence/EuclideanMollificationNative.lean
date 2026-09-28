import PoincareConjecture.Proofs.M03.Existence.EuclideanTranslationNative
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator










set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff

namespace PoincareConjecture.EuclideanMollificationNative

open EuclideanTranslationNative

variable {n : ℕ} {ε : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def mollifierBump (hε : 0 < ε) : ContDiffBump (0 : E) where
  rIn := ε / 3
  rOut := ε
  rIn_pos := div_pos hε (by norm_num)
  rIn_lt_rOut := by linarith

def mollifier (hε : 0 < ε) : E → ℝ := (mollifierBump (n := n) hε).normed volume

theorem mollifier_nonneg (hε : 0 < ε) (x : E) : 0 ≤ mollifier hε x :=
  (mollifierBump hε).nonneg_normed x

theorem mollifier_contDiff (hε : 0 < ε) : ContDiff ℝ ∞ (mollifier (n := n) hε) :=
  (mollifierBump hε).contDiff_normed

theorem mollifier_continuous (hε : 0 < ε) : Continuous (mollifier (n := n) hε) :=
  (mollifierBump hε).continuous_normed

theorem mollifier_even (hε : 0 < ε) (x : E) : mollifier hε (-x) = mollifier hε x :=
  (mollifierBump hε).normed_neg x

theorem mollifier_compactSupport (hε : 0 < ε) : HasCompactSupport (mollifier (n := n) hε) :=
  (mollifierBump hε).hasCompactSupport_normed

theorem mollifier_integrable (hε : 0 < ε) : Integrable (mollifier (n := n) hε) volume :=
  (mollifierBump hε).integrable_normed

theorem mollifier_integral (hε : 0 < ε) : ∫ x, mollifier (n := n) hε x = 1 :=
  (mollifierBump hε).integral_normed

theorem mollifier_memLp (hε : 0 < ε) : MemLp (mollifier (n := n) hε) 2 volume :=
  (mollifier_continuous hε).memLp_of_hasCompactSupport (mollifier_compactSupport hε)

theorem norm_le_of_mollifier_ne_zero (hε : 0 < ε) {x : E}
    (hx : mollifier hε x ≠ 0) : ‖x‖ ≤ ε := by
  have hmem : x ∈ Function.support (mollifier hε) := hx
  rw [mollifier, (mollifierBump hε).support_normed_eq] at hmem
  exact (show ‖x‖ < ε by
    simpa only [Metric.mem_ball, dist_zero_right, mollifierBump] using hmem).le

theorem continuous_translateLp (F : ScalarL2 n) : Continuous (fun h : E => translateLp h F) := by
  let shift : C(E, C(E, E)) :=
    (⟨fun p : E × E => p.2 + p.1, continuous_snd.add continuous_fst⟩ : C(E × E, E)).curry
  exact continuous_const.compMeasurePreservingLp shift.continuous
    (fun h => measurePreserving_add_right volume h) (by norm_num)

def mollifierKernel (hε : 0 < ε) (x : E) : ScalarL2 n :=
  translateLp (-x) ((mollifier_memLp hε).toLp (mollifier hε))

theorem continuous_mollifierKernel (hε : 0 < ε) :
    Continuous (mollifierKernel (n := n) hε) :=
  (continuous_translateLp ((mollifier_memLp hε).toLp (mollifier hε))).comp continuous_neg

def mollify (hε : 0 < ε) (F : ScalarL2 n) (x : E) : ℝ :=
  inner ℝ (mollifierKernel hε x) F

theorem continuous_mollify (hε : 0 < ε) (F : ScalarL2 n) : Continuous (mollify hε F) :=
  (continuous_mollifierKernel hε).inner continuous_const


theorem mollify_toLp_eq_integral (hε : 0 < ε) {f : E → ℝ}
    (hf : MemLp f 2 volume) (x : E) :
    mollify hε (hf.toLp f) x = ∫ h, mollifier hε h * f (x - h) := by
  have htranslate := (mollifier_memLp (n := n) hε).comp_measurePreserving
    (measurePreserving_add_right volume (-x))
  change inner ℝ (Lp.compMeasurePreserving (fun y : E => y + -x)
    (measurePreserving_add_right volume (-x))
    ((mollifier_memLp hε).toLp (mollifier hε))) (hf.toLp f) = _
  rw [Lp.toLp_compMeasurePreserving, L2.inner_def]
  calc
    _ = ∫ y, mollifier hε (y - x) * f y := by
      apply integral_congr_ae
      filter_upwards [htranslate.coeFn_toLp, hf.coeFn_toLp] with y hφ hf'
      rw [hφ, hf']
      simp only [Function.comp_apply, sub_eq_add_neg, RCLike.inner_apply,
        conj_trivial, mul_comm]
    _ = ∫ h, mollifier hε ((x - h) - x) * f (x - h) :=
      (integral_sub_left_eq_self (fun y => mollifier hε (y - x) * f y) volume x).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro h
      have heq : (x - h) - x = -h := by abel
      change mollifier hε ((x - h) - x) * f (x - h) = mollifier hε h * f (x - h)
      rw [heq, mollifier_even]


theorem weighted_integral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w q : α → ℝ} (hw : Integrable w μ) (hwq : Integrable (fun x => w x * q x) μ)
    (hwq2 : Integrable (fun x => w x * q x ^ 2) μ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x ∂μ = 1) :
    (∫ x, w x * q x ∂μ) ^ 2 ≤ ∫ x, w x * q x ^ 2 ∂μ := by
  let a : ℝ := ∫ x, w x * q x ∂μ
  have hn : 0 ≤ ∫ x, w x * (q x - a) ^ 2 ∂μ :=
    integral_nonneg (fun x => mul_nonneg (hw0 x) (sq_nonneg _))
  have he : (∫ x, w x * (q x - a) ^ 2 ∂μ) =
      (∫ x, w x * q x ^ 2 ∂μ) - 2 * a * a + a ^ 2 := by
    calc
      _ = ∫ x, w x * q x ^ 2 - (2 * a) * (w x * q x) + a ^ 2 * w x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun _ => by ring)
      _ = _ := by
        have hadd : (∫ x, w x * q x ^ 2 - (2 * a) * (w x * q x) + a ^ 2 * w x ∂μ) =
            (∫ x, w x * q x ^ 2 - (2 * a) * (w x * q x) ∂μ) +
              ∫ x, a ^ 2 * w x ∂μ :=
          integral_add (hwq2.sub (hwq.const_mul (2 * a))) (hw.const_mul (a ^ 2))
        have hsub : (∫ x, w x * q x ^ 2 - (2 * a) * (w x * q x) ∂μ) =
            (∫ x, w x * q x ^ 2 ∂μ) - ∫ x, (2 * a) * (w x * q x) ∂μ :=
          integral_sub hwq2 (hwq.const_mul (2 * a))
        rw [hadd, hsub, integral_const_mul, integral_const_mul, hw1]
        dsimp only [a]
        ring
  rw [he] at hn
  change a ^ 2 ≤ _
  nlinarith

theorem integrable_mollifier_mul_continuous (hε : 0 < ε) {q : E → ℝ}
    (hq : Continuous q) : Integrable (fun x => mollifier hε x * q x) volume :=
  ((mollifier_continuous hε).mul hq).integrable_of_hasCompactSupport
    (mollifier_compactSupport hε).mul_right

theorem mollify_sub_eq_integral (hε : 0 < ε) {f : E → ℝ}
    (hf : Continuous f) (hfL2 : MemLp f 2 volume) (x : E) :
    mollify hε (hfL2.toLp f) x - f x =
      ∫ h, mollifier hε h * (f (x - h) - f x) := by
  rw [mollify_toLp_eq_integral]
  simp_rw [mul_sub]
  have hi : Integrable (fun h => mollifier hε h * f (x - h)) volume :=
    integrable_mollifier_mul_continuous hε
      (hf.comp (continuous_const.sub continuous_id))
  rw [integral_sub hi ((mollifier_integrable hε).mul_const (f x)),
    integral_mul_const, mollifier_integral, one_mul]

theorem mollify_error_sq_le (hε : 0 < ε) {f : E → ℝ}
    (hf : Continuous f) (hfL2 : MemLp f 2 volume) (x : E) :
    (mollify hε (hfL2.toLp f) x - f x) ^ 2 ≤
      ∫ h, mollifier hε h * (f (x - h) - f x) ^ 2 := by
  rw [mollify_sub_eq_integral hε hf hfL2 x]
  have hq : Continuous (fun h => f (x - h) - f x) :=
    (hf.comp (continuous_const.sub continuous_id)).sub continuous_const
  exact weighted_integral_sq_le (mollifier_integrable hε)
    (integrable_mollifier_mul_continuous hε hq)
    (integrable_mollifier_mul_continuous hε (hq.pow 2))
    (mollifier_nonneg hε) (mollifier_integral hε)

def gradientEnergy (f : E → ℝ) : ℝ :=
  ∑ i, ∫ x, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2

theorem gradientEnergy_nonneg (f : E → ℝ) : 0 ≤ gradientEnergy f :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

theorem integral_sub_translation_sq_le {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) (h : E) :
    (∫ x, (f (x - h) - f x) ^ 2) ≤ ‖h‖ ^ 2 * gradientEnergy f := by
  have hdir := integral_translation_sq_le_directional hf hfL2 (-h)
    (memLp_directional_of_coordinates hcoord (-h))
  have he := hdir.trans (integral_directional_sq_le_coordinates hcoord (-h))
  simpa only [sub_eq_add_neg, norm_neg, gradientEnergy] using he

theorem weighted_translation_energy_le (hε : 0 < ε) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) (h : E) :
    mollifier hε h * (∫ x, (f (x - h) - f x) ^ 2) ≤
      mollifier hε h * (ε ^ 2 * gradientEnergy f) := by
  by_cases hz : mollifier hε h = 0
  · simp only [hz, zero_mul, le_refl]
  · apply mul_le_mul_of_nonneg_left _ (mollifier_nonneg hε h)
    exact (integral_sub_translation_sq_le hf hfL2 hcoord h).trans
      (mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg h) hε.le).mpr (norm_le_of_mollifier_ne_zero hε hz))
        (gradientEnergy_nonneg f))

theorem integrable_weighted_translation_sq (hε : 0 < ε) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) :
    Integrable (fun p : E × E => mollifier hε p.1 * (f (p.2 - p.1) - f p.2) ^ 2)
      (volume.prod volume) := by
  have hc : Continuous
      (fun p : E × E => mollifier hε p.1 * (f (p.2 - p.1) - f p.2) ^ 2) :=
    ((mollifier_continuous hε).comp continuous_fst).mul
      (((hf.continuous.comp (continuous_snd.sub continuous_fst)).sub
        (hf.continuous.comp continuous_snd)).pow 2)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro h
    have hd := (hfL2.comp_measurePreserving
      (measurePreserving_add_right volume (-h))).sub hfL2
    simpa only [Function.comp_apply, Pi.sub_apply, sub_eq_add_neg] using
      hd.integrable_sq.const_mul (mollifier hε h)
  · apply ((mollifier_integrable (n := n) hε).mul_const
      (ε ^ 2 * gradientEnergy f)).mono' hc.aestronglyMeasurable.norm.integral_prod_right'
    apply Eventually.of_forall
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs,
      abs_of_nonneg (mollifier_nonneg hε h), integral_const_mul]
    exact weighted_translation_energy_le hε hf hfL2 hcoord h

theorem integrable_mollify_error_sq (hε : 0 < ε) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) :
    Integrable (fun x => (mollify hε (hfL2.toLp f) x - f x) ^ 2) volume := by
  apply (integrable_weighted_translation_sq hε hf hfL2 hcoord).integral_prod_right.mono'
    (((continuous_mollify hε (hfL2.toLp f)).sub hf.continuous).pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖(mollify hε (hfL2.toLp f) x - f x) ^ 2‖ ≤
    ∫ h, mollifier hε h * (f (x - h) - f x) ^ 2
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  exact mollify_error_sq_le hε hf.continuous hfL2 x


theorem integral_mollify_error_sq_le (hε : 0 < ε) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) :
    (∫ x, (mollify hε (hfL2.toLp f) x - f x) ^ 2) ≤ ε ^ 2 * gradientEnergy f := by
  have hi := integrable_weighted_translation_sq hε hf hfL2 hcoord
  calc
    _ ≤ ∫ x, ∫ h, mollifier hε h * (f (x - h) - f x) ^ 2 :=
      integral_mono (integrable_mollify_error_sq hε hf hfL2 hcoord)
        hi.integral_prod_right (mollify_error_sq_le hε hf.continuous hfL2)
    _ = ∫ h, ∫ x, mollifier hε h * (f (x - h) - f x) ^ 2 :=
      (integral_integral_swap hi).symm
    _ ≤ ∫ h, mollifier hε h * (ε ^ 2 * gradientEnergy f) := by
      apply integral_mono hi.integral_prod_left ((mollifier_integrable hε).mul_const _)
      intro h
      change (∫ x, mollifier hε h * (f (x - h) - f x) ^ 2) ≤
        mollifier hε h * (ε ^ 2 * gradientEnergy f)
      rw [integral_const_mul]
      exact weighted_translation_energy_le hε hf hfL2 hcoord h
    _ = _ := by rw [integral_mul_const, mollifier_integral, one_mul]

end PoincareConjecture.EuclideanMollificationNative
