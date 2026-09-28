import PoincareConjecture.Proofs.M03.Existence.EuclideanSobolevRegularityNative
import Mathlib.Analysis.Distribution.FourierMultiplier

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory FourierTransform
open scoped Topology SchwartzMap Laplacian LineDeriv BoundedContinuousFunction

namespace PoincareConjecture.EuclideanFourierCoordinatesNative

open EuclideanSobolevContinuousNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def growthWeight (s : ℝ) (x : E) : ℂ := ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)

theorem growthWeight_hasTemperateGrowth (s : ℝ) :
    (growthWeight (n := n) s).HasTemperateGrowth := by
  unfold growthWeight
  fun_prop

def weightedFourier (s : ℝ) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (growthWeight s)).comp (fourierCLM ℂ 𝓢(E, ℂ))

@[simp] theorem weightedFourier_apply (s : ℝ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedFourier s f x = growthWeight s x * 𝓕 f x :=
  SchwartzMap.smulLeftCLM_apply_apply (growthWeight_hasTemperateGrowth s) (𝓕 f) x

def frequencyCoordinates (s : ℝ) : 𝓢(E, ℂ) →L[ℂ] FrequencyL2 n :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp (weightedFourier s)

theorem frequencyCoordinates_ae_eq (s : ℝ) (f : 𝓢(E, ℂ)) :
    frequencyCoordinates s f =ᵐ[volume] (fun x => growthWeight s x * 𝓕 f x) := by
  filter_upwards [(weightedFourier s f).coeFn_toLp 2] with x hx
  exact hx.trans (weightedFourier_apply s f x)

theorem decayWeight_mul_growthWeight (s : ℝ) (x : E) :
    (decayWeight s x : ℂ) * growthWeight s x = 1 := by
  unfold decayWeight growthWeight
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2)]
  simp only [show -s / 2 + s / 2 = 0 by ring, Real.rpow_zero, Complex.ofReal_one]

theorem sobolevRealization_frequencyCoordinates {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (f : 𝓢(E, ℂ)) :
    (sobolevRealization hs (frequencyCoordinates s f) : E → ℂ) = f := by
  apply sobolevRealization_eq_of_fourier hs (frequencyCoordinates s f)
    f.continuous f.integrable
  · simpa only [SchwartzMap.fourier_coe] using (𝓕 f).integrable
  · filter_upwards [frequencyCoordinates_ae_eq s f] with x hx
    simp only [hx, ← mul_assoc, decayWeight_mul_growthWeight s x, one_mul,
      SchwartzMap.fourier_coe]

@[simp] theorem weightedFourier_zero (f : 𝓢(E, ℂ)) : weightedFourier 0 f = 𝓕 f := by
  ext x
  simp [growthWeight]

theorem norm_frequencyCoordinates_zero (f : 𝓢(E, ℂ)) :
    ‖frequencyCoordinates 0 f‖ = ‖f.toLp 2‖ := by
  simp only [frequencyCoordinates, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply,
    weightedFourier_zero, SchwartzMap.norm_fourier_toL2_eq]

def laplacianFactor : ℝ := ((2 * Real.pi) ^ 2)⁻¹

theorem laplacianFactor_nonneg : 0 ≤ laplacianFactor := by
  unfold laplacianFactor
  positivity

theorem laplacianFactor_cancel :
    (laplacianFactor : ℂ) * ((-((2 * Real.pi) ^ 2) : ℝ) : ℂ) = -1 := by
  have hp : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  have hreal : laplacianFactor * (-((2 * Real.pi) ^ 2)) = -(1 : ℝ) := by
    rw [laplacianFactor, mul_neg, inv_mul_cancel₀ hp]
  simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one] using
    congrArg Complex.ofReal hreal

theorem growthWeight_add_two (s : ℝ) (x : E) :
    growthWeight (s + 2) x = growthWeight s x * ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) := by
  unfold growthWeight
  rw [show (s + 2) / 2 = s / 2 + 1 by ring,
    Real.rpow_add (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2), Real.rpow_one, Complex.ofReal_mul]

theorem fourier_laplacian_apply (f : 𝓢(E, ℂ)) (x : E) :
    𝓕 (Δ f) x = ((-((2 * Real.pi) ^ 2) : ℝ) : ℂ) *
      ((‖x‖ ^ 2 : ℝ) : ℂ) * 𝓕 f x := by
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM, fourier_smul]
  simp only [SchwartzMap.smul_apply, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (by fun_prop : (fun y : E => ‖y‖ ^ 2).HasTemperateGrowth),
    Complex.real_smul, smul_eq_mul, mul_assoc]

theorem weightedFourier_add_two (s : ℝ) (f : 𝓢(E, ℂ)) :
    weightedFourier (s + 2) f =
      weightedFourier s f - (laplacianFactor : ℂ) • weightedFourier s (Δ f) := by
  ext x
  simp only [weightedFourier_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply,
    smul_eq_mul, growthWeight_add_two, fourier_laplacian_apply]
  have hcancel := laplacianFactor_cancel
  have hexpand : ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) = 1 + ((‖x‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hexpand]
  linear_combination (growthWeight s x * ((‖x‖ ^ 2 : ℝ) : ℂ) * 𝓕 f x) * hcancel

def coordinateSecond (i : Fin n) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  ∂_{EuclideanSpace.single i (1 : ℝ)} (∂_{EuclideanSpace.single i (1 : ℝ)} f)

theorem sum_coordinateSecond (f : 𝓢(E, ℂ)) :
    (∑ i : Fin n, coordinateSecond i f) = Δ f := by
  simpa only [coordinateSecond, EuclideanSpace.basisFun_apply] using
    (SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ) f).symm

theorem frequencyCoordinates_add_two (s : ℝ) (f : 𝓢(E, ℂ)) :
    frequencyCoordinates (s + 2) f = frequencyCoordinates s f -
      (laplacianFactor : ℂ) • ∑ i : Fin n, frequencyCoordinates s (coordinateSecond i f) := by
  have h := congrArg (SchwartzMap.toLpCLM ℂ ℂ 2 volume) (weightedFourier_add_two s f)
  change frequencyCoordinates (s + 2) f =
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume)
      (weightedFourier s f - (laplacianFactor : ℂ) • weightedFourier s (Δ f)) at h
  rw [map_sub, map_smul] at h
  change frequencyCoordinates (s + 2) f = frequencyCoordinates s f -
    (laplacianFactor : ℂ) • frequencyCoordinates s (Δ f) at h
  rw [← sum_coordinateSecond, map_sum] at h
  exact h

def derivativeBudget : ℕ → 𝓢(E, ℂ) → ℝ
  | 0, f => ‖f.toLp 2‖
  | m + 1, f => derivativeBudget m f +
      laplacianFactor * ∑ i : Fin n, derivativeBudget m (coordinateSecond i f)

theorem derivativeBudget_nonneg (m : ℕ) (f : 𝓢(E, ℂ)) : 0 ≤ derivativeBudget m f := by
  induction m generalizing f with
  | zero => exact norm_nonneg _
  | succ m ih =>
      exact add_nonneg (ih f) (mul_nonneg laplacianFactor_nonneg
        (Finset.sum_nonneg (fun i _ => ih (coordinateSecond i f))))

theorem norm_frequencyCoordinates_even_le (m : ℕ) (f : 𝓢(E, ℂ)) :
    ‖frequencyCoordinates (2 * (m : ℝ)) f‖ ≤ derivativeBudget m f := by
  induction m generalizing f with
  | zero => simpa only [Nat.cast_zero, mul_zero, derivativeBudget] using
      (norm_frequencyCoordinates_zero f).le
  | succ m ih =>
      rw [Nat.cast_add_one, mul_add, mul_one, frequencyCoordinates_add_two]
      calc
        _ ≤ ‖frequencyCoordinates (2 * (m : ℝ)) f‖ +
            ‖(laplacianFactor : ℂ) •
              ∑ i : Fin n, frequencyCoordinates (2 * (m : ℝ)) (coordinateSecond i f)‖ :=
          norm_sub_le _ _
        _ = ‖frequencyCoordinates (2 * (m : ℝ)) f‖ + laplacianFactor *
            ‖∑ i : Fin n, frequencyCoordinates (2 * (m : ℝ)) (coordinateSecond i f)‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg laplacianFactor_nonneg]
        _ ≤ derivativeBudget m f + laplacianFactor *
            ∑ i : Fin n, derivativeBudget m (coordinateSecond i f) := by
          apply add_le_add (ih f)
          apply mul_le_mul_of_nonneg_left _ laplacianFactor_nonneg
          exact (norm_sum_le Finset.univ _).trans
            (Finset.sum_le_sum (fun i _ => ih (coordinateSecond i f)))
        _ = _ := rfl

theorem norm_schwartz_sup_le_derivativeBudget (m : ℕ) (hm : (n : ℝ) < 2 * (2 * (m : ℝ)))
    (f : 𝓢(E, ℂ)) :
    ‖f.toBoundedContinuousFunction‖ ≤ ‖decayLp hm‖ * derivativeBudget m f := by
  have heq : sobolevRealization hm (frequencyCoordinates (2 * (m : ℝ)) f) =
      f.toBoundedContinuousFunction := by
    ext x
    exact congrFun (sobolevRealization_frequencyCoordinates hm f) x
  rw [← heq]
  exact (norm_sobolevRealization_le hm _).trans
    (mul_le_mul_of_nonneg_left (norm_frequencyCoordinates_even_le m f) (norm_nonneg _))

theorem norm_iteratedFDeriv_schwartz_le_derivativeBudget (m k : ℕ)
    (hm : (n : ℝ) < 2 * (2 * (m : ℝ) - k)) (f : 𝓢(E, ℂ)) (x : E) :
    ‖iteratedFDeriv ℝ k (f : E → ℂ) x‖ ≤
      ((2 * Real.pi * ‖(-innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖) ^ k *
        ‖momentLp k hm‖) * derivativeBudget m f := by
  have hs : (n : ℝ) < 2 * (2 * (m : ℝ)) := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hbound := norm_iteratedFDeriv_sobolevRealization_le k hs hm
    (frequencyCoordinates (2 * (m : ℝ)) f) x
  rw [sobolevRealization_frequencyCoordinates hs f] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (norm_frequencyCoordinates_even_le m f)
    (by positivity))

theorem realSobolevRealization_frequencyCoordinates {s : ℝ} (hs : (n : ℝ) < 2 * s)
    (f : 𝓢(E, ℝ)) :
    (realSobolevRealization hs
      (frequencyCoordinates s (SchwartzMap.postcompCLM Complex.ofRealCLM f)) : E → ℝ) = f := by
  funext x
  have h := congrArg Complex.re
    (congrFun (sobolevRealization_frequencyCoordinates hs
      (SchwartzMap.postcompCLM Complex.ofRealCLM f)) x)
  simpa only [realSobolevRealization_apply, SchwartzMap.postcompCLM_apply,
    Complex.ofRealCLM_apply, Complex.ofReal_re] using h

end PoincareConjecture.EuclideanFourierCoordinatesNative
