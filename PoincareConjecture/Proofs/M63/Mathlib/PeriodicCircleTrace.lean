import PoincareConjecture.Proofs.M63.Mathlib.PeriodicFourierTrace










set_option autoImplicit false

open AddCircle
open scoped ENNReal

namespace PoincareConjecture.M63




theorem memℓp_second_weight_circle {L : ℝ} [Fact (0 < L)] (f : C(AddCircle L, ℂ))
    (hf : ContDiff ℝ 2 (fun x : ℝ => f (x : AddCircle L))) :
    Memℓp (fun n : ℤ => ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
      fourierCoeff f n) 2 := by
  have hperiod : Function.Periodic (fun x : ℝ => f (x : AddCircle L)) L := by
    intro x
    dsimp only
    rw [coe_add_period]
  have hc (n : ℤ) :
      fourierCoeffOn (Fact.out : 0 < L) (fun x : ℝ => f (x : AddCircle L)) n =
        fourierCoeff f n := by
    rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral f n 0]
    simp only [fourier_coe_apply, sub_zero, zero_add]
  simpa only [hc] using
    memℓp_second_weight_of_contDiff_periodic (Fact.out : 0 < L) hf hperiod

end PoincareConjecture.M63
