import PoincareConjecture.Proofs.M03.Existence.EuclideanSobolevContinuousNative
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory FourierTransform
open scoped Topology BoundedContinuousFunction ContDiff

namespace PoincareConjecture.EuclideanSobolevContinuousNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def momentWeight (j : ℕ) (s : ℝ) (x : E) : ℝ := ‖x‖ ^ j * decayWeight s x

theorem continuous_momentWeight (j : ℕ) (s : ℝ) :
    Continuous (momentWeight (n := n) j s) :=
  (continuous_norm.pow j).mul (continuous_decayWeight s)

theorem sq_momentWeight_le (j : ℕ) (s : ℝ) (x : E) :
    momentWeight j s x ^ 2 ≤ (1 + ‖x‖ ^ 2) ^ (-(s - j)) := by
  have hb : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  calc
    momentWeight j s x ^ 2 = (‖x‖ ^ 2) ^ j * (1 + ‖x‖ ^ 2) ^ (-s) := by
      unfold momentWeight decayWeight
      rw [mul_pow, pow_right_comm,
        ← Real.rpow_mul_natCast hb.le]
      congr 2
      ring
    _ ≤ (1 + ‖x‖ ^ 2) ^ j * (1 + ‖x‖ ^ 2) ^ (-s) := by
      gcongr
      linarith
    _ = (1 + ‖x‖ ^ 2) ^ (-(s - j)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hb]
      congr 1
      ring

theorem memLp_momentWeight (j : ℕ) {s : ℝ} (hs : (n : ℝ) < 2 * (s - j)) :
    MemLp (momentWeight (n := n) j s) 2 volume := by
  apply (memLp_two_iff_integrable_sq (μ := (volume : Measure E))
    (continuous_momentWeight j s).aestronglyMeasurable).mpr
  have hint0 : Integrable (fun x : E => (1 + ‖x‖ ^ 2) ^ (-(2 * (s - j)) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using hs)
  have hint : Integrable (fun x : E => (1 + ‖x‖ ^ 2) ^ (-(s - j))) volume := by
    apply hint0.congr
    filter_upwards with x
    congr 1
    ring
  apply hint.mono' ((continuous_momentWeight j s).pow 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_momentWeight_le j s x

theorem integrable_frequencyMoment (j : ℕ) {s : ℝ}
    (hs : (n : ℝ) < 2 * (s - j)) (u : FrequencyL2 n) :
    Integrable (fun x : E => ‖x‖ ^ j * ‖(decayWeight s x : ℂ) * u x‖) volume := by
  have hm : MemLp (fun x : E => momentWeight j s x * ‖u x‖) 1 volume :=
    (Lp.memLp u).norm.mul' (memLp_momentWeight j hs)
  apply (memLp_one_iff_integrable.mp hm).congr
  filter_upwards with x
  simp only [momentWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (decayWeight_pos s x)]
  ring

def momentLp (j : ℕ) {s : ℝ} (hs : (n : ℝ) < 2 * (s - j)) : FrequencyL2 n :=
  (memLp_momentWeight j hs).ofReal.toLp (fun x => (momentWeight j s x : ℂ))

theorem momentLp_ae_eq (j : ℕ) {s : ℝ} (hs : (n : ℝ) < 2 * (s - j)) :
    momentLp j hs =ᵐ[volume] (fun x : E => (momentWeight j s x : ℂ)) :=
  (memLp_momentWeight j hs).ofReal.coeFn_toLp

theorem integral_frequencyMoment_le (j : ℕ) {s : ℝ}
    (hs : (n : ℝ) < 2 * (s - j)) (u : FrequencyL2 n) :
    (∫ x : E, ‖x‖ ^ j * ‖(decayWeight s x : ℂ) * u x‖) ≤
      ‖momentLp j hs‖ * ‖u‖ := by
  calc
    _ = ∫ x : E, ‖weightedL1 (momentLp j hs) u x‖ := by
      apply integral_congr_ae
      filter_upwards [weightedL1_ae_eq (momentLp j hs) u, momentLp_ae_eq j hs] with x hx hw
      rw [hx, hw]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (decayWeight_pos s x)]
      unfold momentWeight
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) j)
        (decayWeight_pos s x).le)]
      ring
    _ = ‖weightedL1 (momentLp j hs) u‖ := (L1.norm_eq_integral_norm _).symm
    _ ≤ _ := norm_weightedL1_le _ _

theorem iteratedFDeriv_inverseFourier (k : ℕ) {f : E → ℂ}
    (hf : ∀ j : ℕ, j ≤ k → Integrable (fun x : E => ‖x‖ ^ j * ‖f x‖))
    (hm : AEStronglyMeasurable f) :
    iteratedFDeriv ℝ k (𝓕⁻ f) =
      𝓕⁻ (fun x => VectorFourier.fourierPowSMulRight (-innerSL ℝ) f x k) := by
  apply VectorFourier.iteratedFDeriv_fourierIntegral (-innerSL ℝ) (N := (k : ℕ∞))
  · intro j hj
    exact hf j (by exact_mod_cast hj)
  · exact hm
  · exact le_rfl

theorem norm_iteratedFDeriv_inverseFourier_le (k : ℕ) {f : E → ℂ}
    (hf : ∀ j : ℕ, j ≤ k → Integrable (fun x : E => ‖x‖ ^ j * ‖f x‖))
    (hm : AEStronglyMeasurable f) (x : E) :
    ‖iteratedFDeriv ℝ k (𝓕⁻ f) x‖ ≤
      (2 * Real.pi * ‖(-innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖) ^ k *
        ∫ y : E, ‖y‖ ^ k * ‖f y‖ := by
  rw [iteratedFDeriv_inverseFourier k hf hm]
  have hi := VectorFourier.integrable_fourierPowSMulRight (-innerSL ℝ) (hf k le_rfl) hm
  calc
    _ ≤ ∫ y : E, ‖VectorFourier.fourierPowSMulRight (-innerSL ℝ) f y k‖ := by
      rw [Real.fourierInv_eq]
      apply (norm_integral_le_integral_norm _).trans_eq
      apply integral_congr_ae
      filter_upwards with y
      exact Circle.norm_smul _ _
    _ ≤ ∫ y : E,
        (2 * Real.pi * ‖(-innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖) ^ k *
          (‖y‖ ^ k * ‖f y‖) := by
      apply integral_mono hi.norm ((hf k le_rfl).const_mul _)
      intro y
      simpa only [mul_assoc] using
        VectorFourier.norm_fourierPowSMulRight_le (-innerSL ℝ) f y k
    _ = _ := integral_const_mul _ _

theorem contDiff_sobolevRealization (k : ℕ) {s : ℝ}
    (hs : (n : ℝ) < 2 * s) (hsk : (n : ℝ) < 2 * (s - k))
    (u : FrequencyL2 n) : ContDiff ℝ k (sobolevRealization hs u : E → ℂ) := by
  have hF : ContDiff ℝ (k : ℕ∞)
      (𝓕 (fun x : E => (decayWeight s x : ℂ) * u x)) := by
    apply Real.contDiff_fourier
    intro j hj
    have hjk : j ≤ k := by exact_mod_cast hj
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    exact integrable_frequencyMoment j (by linarith) u
  have heq : (sobolevRealization hs u : E → ℂ) =
      fun x => (𝓕 (fun y : E => (decayWeight s y : ℂ) * u y)) (-x) := by
    funext x
    rw [sobolevRealization_apply, Real.fourierInv_eq_fourier_neg]
  rw [heq]
  exact hF.comp (contDiff_id.neg)

theorem contDiff_realSobolevRealization (k : ℕ) {s : ℝ}
    (hs : (n : ℝ) < 2 * s) (hsk : (n : ℝ) < 2 * (s - k))
    (u : FrequencyL2 n) : ContDiff ℝ k (realSobolevRealization hs u : E → ℝ) :=
  Complex.reCLM.contDiff.comp (contDiff_sobolevRealization k hs hsk u)

theorem norm_iteratedFDeriv_sobolevRealization_le (k : ℕ) {s : ℝ}
    (hs : (n : ℝ) < 2 * s) (hsk : (n : ℝ) < 2 * (s - k))
    (u : FrequencyL2 n) (x : E) :
    ‖iteratedFDeriv ℝ k (sobolevRealization hs u : E → ℂ) x‖ ≤
      ((2 * Real.pi * ‖(-innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)‖) ^ k *
        ‖momentLp k hsk‖) * ‖u‖ := by
  have heq : (sobolevRealization hs u : E → ℂ) =
      𝓕⁻ (fun y : E => (decayWeight s y : ℂ) * u y) := by
    funext y
    exact sobolevRealization_apply hs u y
  rw [heq]
  have hf (j : ℕ) (hj : j ≤ k) : Integrable
      (fun y : E => ‖y‖ ^ j * ‖(decayWeight s y : ℂ) * u y‖) := by
    have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
    exact integrable_frequencyMoment j (by linarith) u
  have hm : AEStronglyMeasurable (fun y : E => (decayWeight s y : ℂ) * u y) :=
    (Complex.continuous_ofReal.comp (continuous_decayWeight s)).aestronglyMeasurable.mul
      (Lp.stronglyMeasurable u).aestronglyMeasurable
  exact (norm_iteratedFDeriv_inverseFourier_le k hf hm x).trans
    ((mul_le_mul_of_nonneg_left (integral_frequencyMoment_le k hsk u) (by positivity)).trans_eq
      (mul_assoc _ _ _).symm)

end PoincareConjecture.EuclideanSobolevContinuousNative
