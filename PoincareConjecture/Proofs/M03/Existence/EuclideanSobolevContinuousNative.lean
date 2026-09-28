import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space









set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory FourierTransform
open scoped Topology BoundedContinuousFunction

namespace PoincareConjecture.EuclideanSobolevContinuousNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

abbrev FrequencyL2 (n : ℕ) := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))

abbrev FrequencyL1 (n : ℕ) := Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Fin n)))


def weightedL1 (w : FrequencyL2 n) : FrequencyL2 n →L[ℂ] FrequencyL1 n :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1 w

theorem weightedL1_ae_eq (w u : FrequencyL2 n) :
    weightedL1 w u =ᵐ[volume] (fun x => w x * u x) :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder w u

theorem norm_weightedL1_le (w u : FrequencyL2 n) :
    ‖weightedL1 w u‖ ≤ ‖w‖ * ‖u‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖w‖ * ‖u‖ :=
      (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le w u
    _ ≤ 1 * ‖w‖ * ‖u‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) (norm_nonneg w))
      (norm_nonneg u)
    _ = _ := by rw [one_mul]

theorem norm_inverseFourier_le (f : FrequencyL1 n) :
    ‖Real.Lp.fourierTransformInvCLM E ℂ f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  rw [Real.Lp.fourierTransformInvCLM_apply, Real.Lp.fourierTransformInv_apply,
    Real.fourierInv_eq]
  calc
    _ ≤ ∫ y, ‖Real.fourierChar (inner ℝ y x) • f y‖ := norm_integral_le_integral_norm _
    _ = ∫ y, ‖f y‖ := by simp only [Circle.norm_smul]
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm


def weightedInverse (w : FrequencyL2 n) : FrequencyL2 n →L[ℂ] E →ᵇ ℂ :=
  (Real.Lp.fourierTransformInvCLM E ℂ).comp (weightedL1 w)

theorem norm_weightedInverse_le (w u : FrequencyL2 n) :
    ‖weightedInverse w u‖ ≤ ‖w‖ * ‖u‖ :=
  (norm_inverseFourier_le (weightedL1 w u)).trans (norm_weightedL1_le w u)

theorem weightedInverse_apply (w u : FrequencyL2 n) (x : E) :
    weightedInverse w u x = 𝓕⁻ (fun y => w y * u y) x := by
  change Real.Lp.fourierTransformInvCLM E ℂ (weightedL1 w u) x = _
  rw [Real.Lp.fourierTransformInvCLM_apply, Real.Lp.fourierTransformInv_apply]
  exact Real.fourierInv_congr_ae (weightedL1_ae_eq w u) x


theorem weightedInverse_eq_of_fourier (w u : FrequencyL2 n) {f : E → ℂ}
    (hf : Continuous f) (hfi : Integrable f) (hF : Integrable (𝓕 f))
    (hcoord : (fun y => w y * u y) =ᵐ[volume] 𝓕 f) :
    (weightedInverse w u : E → ℂ) = f := by
  funext x
  rw [weightedInverse_apply]
  exact (Real.fourierInv_congr_ae hcoord x).trans
    (hfi.fourierInv_fourier_eq hF hf.continuousAt)

def decayWeight (s : ℝ) (x : E) : ℝ := (1 + ‖x‖ ^ 2) ^ (-s / 2)

theorem decayWeight_pos (s : ℝ) (x : E) : 0 < decayWeight s x := by
  unfold decayWeight
  positivity

theorem continuous_decayWeight (s : ℝ) : Continuous (decayWeight (n := n) s) := by
  unfold decayWeight
  apply (continuous_const.add (continuous_norm.pow 2)).rpow_const
  intro x
  exact Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2))


theorem memLp_decayWeight {s : ℝ} (hs : (n : ℝ) < 2 * s) :
    MemLp (decayWeight (n := n) s) 2 volume := by
  apply (memLp_two_iff_integrable_sq (μ := (volume : Measure E))
    (continuous_decayWeight s).aestronglyMeasurable).mpr
  have hint : Integrable (fun x : E => (1 + ‖x‖ ^ 2) ^ (-(2 * s) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using hs)
  apply hint.congr
  filter_upwards with x
  unfold decayWeight
  rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2)]
  congr 1
  ring

def decayLp {s : ℝ} (hs : (n : ℝ) < 2 * s) : FrequencyL2 n :=
  (memLp_decayWeight hs).ofReal.toLp (fun x => (decayWeight s x : ℂ))

theorem decayLp_ae_eq {s : ℝ} (hs : (n : ℝ) < 2 * s) :
    decayLp hs =ᵐ[volume] (fun x : E => (decayWeight s x : ℂ)) :=
  (memLp_decayWeight hs).ofReal.coeFn_toLp


def sobolevRealization {s : ℝ} (hs : (n : ℝ) < 2 * s) : FrequencyL2 n →L[ℂ] E →ᵇ ℂ :=
  weightedInverse (decayLp hs)

theorem norm_sobolevRealization_le {s : ℝ} (hs : (n : ℝ) < 2 * s) (u : FrequencyL2 n) :
    ‖sobolevRealization hs u‖ ≤ ‖decayLp hs‖ * ‖u‖ := norm_weightedInverse_le _ _

theorem sobolevRealization_apply {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (u : FrequencyL2 n) (x : E) :
    sobolevRealization hs u x = 𝓕⁻ (fun y => (decayWeight s y : ℂ) * u y) x := by
  rw [sobolevRealization, weightedInverse_apply]
  apply Real.fourierInv_congr_ae _ x
  filter_upwards [decayLp_ae_eq hs] with y hy
  rw [hy]

theorem sobolevRealization_eq_of_fourier {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (u : FrequencyL2 n) {f : E → ℂ} (hf : Continuous f)
    (hfi : Integrable f) (hF : Integrable (𝓕 f))
    (hcoord : (fun y => (decayWeight s y : ℂ) * u y) =ᵐ[volume] 𝓕 f) :
    (sobolevRealization hs u : E → ℂ) = f := by
  apply weightedInverse_eq_of_fourier (decayLp hs) u hf hfi hF
  filter_upwards [decayLp_ae_eq hs, hcoord] with y hy hc
  rw [hy, hc]


def realSobolevRealization {s : ℝ} (hs : (n : ℝ) < 2 * s) :
    FrequencyL2 n →L[ℝ] E →ᵇ ℝ :=
  (Complex.reCLM.compLeftContinuousBounded E).comp ((sobolevRealization hs).restrictScalars ℝ)

@[simp] theorem realSobolevRealization_apply {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (u : FrequencyL2 n) (x : E) :
    realSobolevRealization hs u x = (sobolevRealization hs u x).re := rfl

theorem norm_realSobolevRealization_le {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (u : FrequencyL2 n) :
    ‖realSobolevRealization hs u‖ ≤ ‖decayLp hs‖ * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  rw [realSobolevRealization_apply, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans
    ((BoundedContinuousFunction.norm_coe_le_norm _ _).trans (norm_sobolevRealization_le hs u))

theorem realSobolevRealization_eq_of_fourier {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (u : FrequencyL2 n) {f : E → ℝ} (hf : Continuous f)
    (hfi : Integrable (fun x => (f x : ℂ)))
    (hF : Integrable (𝓕 (fun x => (f x : ℂ))))
    (hcoord : (fun y => (decayWeight s y : ℂ) * u y) =ᵐ[volume]
      𝓕 (fun x => (f x : ℂ))) :
    (realSobolevRealization hs u : E → ℝ) = f := by
  have hrec := sobolevRealization_eq_of_fourier hs u
    (Complex.continuous_ofReal.comp hf) hfi hF hcoord
  funext x
  simpa only [realSobolevRealization_apply, Function.comp_apply, Complex.ofReal_re] using
    congrArg Complex.re (congrFun hrec x)

end PoincareConjecture.EuclideanSobolevContinuousNative
