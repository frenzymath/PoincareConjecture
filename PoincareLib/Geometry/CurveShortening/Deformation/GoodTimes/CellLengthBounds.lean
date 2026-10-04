import PoincareLib.Geometry.CurveShortening.Deformation.Limit.SpeedBounds
import PoincareLib.Geometry.RicciFlow.CurveShortening.Integral.Continuity

/-!
# Actual length noncollapse throughout an enlarged good cell

Morgan--Tian Claim 19.28, printed p. 460; derivation 35 integrates the
actual corrected speed comparisons. This also controls the part of an
enlarged final cell after the earlier noncollapse interval.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

/-- The genuine speed comparison integrates to both actual length
comparisons on an included convex time set; Claim 19.28, printed p. 460.
Speed integrability is established before applying integral monotonicity. -/
theorem m65Length_exp_bounds_on (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 H : ℝ} (bounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {I : Set ℝ} (hI : Convex ℝ I) (hsub : I ⊆ Ioo a b)
    (hcurv : ∀ t ∈ I, ∀ x, m62CurvatureSquared F c t x ≤ H)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    Real.exp (-(K2 + H) * |t - s|) * m62Length F c s ≤ m62Length F c t ∧
      m62Length F c t ≤ Real.exp ((K2 + H) * |t - s|) * m62Length F c s := by
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have his := M62.length_integrable F c hc (Ioo_subset_Icc_self (hsub hs))
  have hit := M62.length_integrable F c hc (Ioo_subset_Icc_self (hsub ht))
  have hpoint := m65Speed_exp_bounds_on c hc bounds hI hsub hcurv hs ht
  constructor
  · have hi := intervalIntegral.integral_mono_on hperiod
      (his.const_mul (Real.exp (-(K2 + H) * |t - s|))) hit
      (fun x _ => (hpoint x).1)
    simpa only [intervalIntegral.integral_const_mul, m62Length] using hi
  · have hi := intervalIntegral.integral_mono_on hperiod hit
      (his.const_mul (Real.exp ((K2 + H) * |t - s|)))
      (fun x _ => (hpoint x).2)
    simpa only [intervalIntegral.integral_const_mul, m62Length] using hi

end PoincareMT
