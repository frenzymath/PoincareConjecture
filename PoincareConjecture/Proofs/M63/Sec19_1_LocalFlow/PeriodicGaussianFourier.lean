import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianHeat
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false

open MeasureTheory AddCircle

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

theorem periodicGaussianHeat_fourier (t : ℝ) (ht : 0 ≤ t) (c : ℂ) (n : ℤ) :
    periodicGaussianHeat t (c • (fourier n : C(AddCircle L, ℂ))) =
      (c * (Real.exp (-(2 * Real.pi * (n : ℝ) / L) ^ 2 * t) : ℂ)) • fourier n := by
  let a : ℂ := ((Real.sqrt Real.pi)⁻¹ : ℝ)
  have hK (s : ℝ) : (gaussianHeatKernel 1 s : ℂ) =
      a * Complex.exp (-(s : ℂ) ^ 2) := by
    simp [gaussianHeatKernel, a, Complex.ofReal_exp]
  have hbase : (∫ s : ℝ, Complex.exp (-(s : ℂ) ^ 2)) =
      (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    simpa using fourierIntegral_gaussian (b := 1) (by norm_num) (0 : ℂ)
  have hmass : a * (Real.pi : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    calc
      _ = ∫ s : ℝ, a * Complex.exp (-(s : ℂ) ^ 2) := by
        rw [integral_const_mul, hbase]
      _ = ∫ s : ℝ, (gaussianHeatKernel 1 s : ℂ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => (hK s).symm)
      _ = 1 := by
        rw [integral_complex_ofReal, integral_gaussianHeatKernel (by norm_num), Complex.ofReal_one]
  have hchar (v : ℝ) :
      (∫ s : ℝ, (gaussianHeatKernel 1 s : ℂ) *
        Complex.exp (Complex.I * (v : ℂ) * s)) = (Real.exp (-v ^ 2 / 4) : ℂ) := by
    have hfour := fourierIntegral_gaussian (b := 1) (by norm_num) (v : ℂ)
    simp only [div_one, mul_one, neg_one_mul] at hfour
    calc
      _ = a * ∫ s : ℝ, Complex.exp (Complex.I * (v : ℂ) * s) *
          Complex.exp (-(s : ℂ) ^ 2) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with s
        rw [hK]
        ring
      _ = a * ((Real.pi : ℂ) ^ (1 / 2 : ℂ) *
          Complex.exp (-(v : ℂ) ^ 2 / 4)) := by rw [hfour]
      _ = (Real.exp (-v ^ 2 / 4) : ℂ) := by
        rw [← mul_assoc, hmass, one_mul, Complex.ofReal_exp]
        congr 1
        push_cast
        rfl
  let w : ℝ := 2 * Real.pi * (n : ℝ) / L
  have hexp : -(-2 * w * Real.sqrt t) ^ 2 / 4 = -w ^ 2 * t := by
    calc
      _ = -w ^ 2 * (Real.sqrt t) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt ht]
  ext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [periodicGaussianHeat_apply]
  have hmode (s : ℝ) :
      gaussianHeatKernel 1 s •
        (c • (fourier n : C(AddCircle L, ℂ)))
          ((x : AddCircle L) - ((2 * Real.sqrt t * s : ℝ) : AddCircle L)) =
      (c * fourier n (x : AddCircle L)) *
        ((gaussianHeatKernel 1 s : ℂ) *
          Complex.exp (Complex.I * ((-2 * w * Real.sqrt t : ℝ) : ℂ) * s)) := by
    rw [← QuotientAddGroup.mk_sub]
    simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.real_smul, fourier_coe_apply]
    have he : 2 * (Real.pi : ℂ) * Complex.I * n *
        ((x - 2 * Real.sqrt t * s : ℝ) : ℂ) / L =
        2 * (Real.pi : ℂ) * Complex.I * n * x / L +
          Complex.I * ((-2 * w * Real.sqrt t : ℝ) : ℂ) * s := by
      dsimp only [w]
      push_cast
      ring
    rw [he, Complex.exp_add]
    ring
  calc
    _ = (c * fourier n (x : AddCircle L)) *
        ∫ s : ℝ, (gaussianHeatKernel 1 s : ℂ) *
          Complex.exp (Complex.I * ((-2 * w * Real.sqrt t : ℝ) : ℂ) * s) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hmode)
    _ = _ := by
      rw [hchar, hexp]
      change (c * fourier n (x : AddCircle L)) * (Real.exp (-w ^ 2 * t) : ℂ) =
        (c * (Real.exp (-w ^ 2 * t) : ℂ)) * fourier n (x : AddCircle L)
      ring

end PoincareConjecture.M63
