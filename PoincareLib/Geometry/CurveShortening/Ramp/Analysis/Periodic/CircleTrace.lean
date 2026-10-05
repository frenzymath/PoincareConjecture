import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.FourierTrace

/-!
# Actual C2 circle data in the Fourier H2 domain

The real lift and the circle have exactly the same normalized Fourier
coefficients. This transfers the proved periodic C2 trace to the actual
circle. MT2007 Claim 19.1, p. 437; contract review block 8 and statement 8
of `2026-09-21-real-periodic-spectral-bridge.md`.
-/

set_option autoImplicit false

open AddCircle
open scoped ENNReal

namespace PoincareMT.M63

/-- The actual coefficients of a C2 circle function have the shifted
second-order weight in lp. MT2007 Claim 19.1, p. 437; real periodic
spectral bridge, statement 8. The Fourier normalization is unchanged. -/
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

end PoincareMT.M63
