import PoincareLib.Geometry.RicciFlow.CurveShortening.Evolution.SpeedEvolution
import PoincareLib.Geometry.RicciFlow.CurveShortening.Estimates.Pointwise
import PoincareLib.Analysis.ODE.LogDerivative

/-!
# Actual parameter-speed bounds on a good cell

Morgan--Tian Claim 19.28, printed pp. 459-460, and the corrected speed
equation in Lemma 0.1 of the 2015 correction, p. 3. Uniform squared
curvature and ambient Ricci bounds control the logarithm of positive
speed on any included convex time set.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

/-- Uniform curvature bounds preserve the actual parameter speed in
both directions on a good cell; Claim 19.28, printed p. 460. -/
theorem m65Speed_exp_bounds_on (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 H : ℝ} (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {I : Set ℝ} (hI : Convex ℝ I) (hsub : I ⊆ Ioo a b)
    (hcurv : ∀ t ∈ I, ∀ x, m62CurvatureSquared F c t x ≤ H)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (x : ℝ) :
    Real.exp (-(K2 + H) * |t - s|) * curveSpeed F c s x ≤ curveSpeed F c t x ∧
      curveSpeed F c t x ≤ Real.exp ((K2 + H) * |t - s|) * curveSpeed F c s x := by
  apply Poincare.exp_bounds_of_abs_deriv_le_mul hI
    (fun r hr => M62.speed_pos F c hc (Ioo_subset_Icc_self (hsub hr)) x)
    (fun r hr => (M62.hasDerivAt_speed F c hc (hsub hr) x).hasDerivWithinAt) ?_ hs ht
  intro r hr
  have htime := Ioo_subset_Icc_self (hsub hr)
  have hunit := (M62.unitTangent_norm F c hc htime x).le
  have hRic : |m62TangentRicci F c r x| ≤ K2 :=
    bounds.ricci r htime (c x r) _ _ hunit hunit
  have hsq := M62.curvatureSquared_nonneg F c r x
  have hcoef : |m62TangentRicci F c r x + m62CurvatureSquared F c r x| ≤ K2 + H :=
    (abs_add_le _ _).trans (by rw [abs_of_nonneg hsq]; exact add_le_add hRic (hcurv r hr x))
  rw [abs_mul, abs_neg, abs_of_pos (M62.speed_pos F c hc htime x)]
  exact mul_le_mul_of_nonneg_right hcoef (M62.speed_nonneg F c r x)

end PoincareMT
