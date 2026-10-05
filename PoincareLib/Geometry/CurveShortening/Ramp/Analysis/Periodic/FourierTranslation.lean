import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.Translation

/-!
# Fourier coefficients under circle translation

Haar translation invariance gives the literal character multiplier.
MT2007 Claim 19.1, p. 437;
`2026-09-21-smooth-spectral-trace-orbit.md`, statement 1.
-/

set_option autoImplicit false

open AddCircle MeasureTheory

namespace PoincareMT.M63

/-- The actual Fourier coefficient of x-to-x-s translation has the
minus-s character phase. MT2007 Claim 19.1, p. 437; smooth spectral
trace orbit, statement 1. Haar invariance and Bochner scalar integration
also cover the totalized nonintegrable case. -/
theorem fourierCoeff_sub_const {L : ℝ} [Fact (0 < L)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : AddCircle L → E) (s : ℝ) (n : ℤ) :
    fourierCoeff (fun x => f (x - (s : AddCircle L))) n =
      fourier n (-(s : AddCircle L)) • fourierCoeff f n := by
  unfold fourierCoeff
  rw [← integral_add_right_eq_self
    (fun x : AddCircle L => fourier (-n) x • f (x - (s : AddCircle L)))
      (s : AddCircle L)]
  have hchar (x : AddCircle L) : fourier (-n) (x + (s : AddCircle L)) =
      fourier n (-(s : AddCircle L)) * fourier (-n) x := by
    simp only [fourier_apply, zsmul_add, neg_zsmul, zsmul_neg,
      toCircle_add, Circle.coe_mul]
    exact mul_comm _ _
  simp_rw [add_sub_cancel_right, hchar, mul_smul]
  exact integral_smul _ _

end PoincareMT.M63
