import PoincareLib.Geometry.CurveShortening.Deformation.Profile.RestartedProfile

/-!
# Additive errors on a good time interval

Claim 19.27, Morgan--Tian p. 459. The integrating factor turns the
approximate restarted-profile comparison into an additive endpoint error.
See M65 derivation 17 for the correction to the printed error recurrence.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Set.Icc a b))

/-- An approximate good-interval comparison contributes its actual additive
weighted error; Claim 19.27, p. 459, with the recurrence corrected. -/
theorem m65RestartedAreaProfile_weighted_comparison
    (s t A fs ft error : ℝ) (h : ft ≤ m65RestartedAreaProfile F s fs t + error) :
    Real.exp (∫ r in a..t, flowScalarCurvatureInfimum F r / 2) *
        (ft - areaComparisonProfile F A t) ≤
      Real.exp (∫ r in a..s, flowScalarCurvatureInfimum F r / 2) *
        (fs - areaComparisonProfile F A s) +
      Real.exp (∫ r in a..t, flowScalarCurvatureInfimum F r / 2) * error := by
  let P : ℝ → ℝ := fun t => ∫ r in a..t, flowScalarCurvatureInfimum F r / 2
  have hdiff := m65RestartedAreaProfile_difference F s fs A t
  have hstep : ft - areaComparisonProfile F A t ≤
      Real.exp (P s - P t) * (fs - areaComparisonProfile F A s) + error := by
    linarith
  have hexp : Real.exp (P t) * Real.exp (P s - P t) = Real.exp (P s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (P t) *
        (Real.exp (P s - P t) * (fs - areaComparisonProfile F A s) + error) :=
      mul_le_mul_of_nonneg_left hstep (Real.exp_nonneg _)
    _ = _ := by rw [mul_add, ← mul_assoc, hexp]

end PoincareMT
