import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Focusing.Transport

/-!
# Uniform norm bound for the spherical focusing field

The transported spherical field has the exact model norm on every regular
radial point.  The elementary bound `sin ≤ 1` turns that identity into the
uniform inverse-scale bound used when integrating endpoint focusing fields.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481. The project derivations
implement its intrinsic normal-geodesic, focusing and retained-length comparison
arguments.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT

/-- The pushed spherical focusing field is bounded by the inverse model scale. The
hypotheses retain the regular radial point and its Gauss identity; no curvature lower or
absolute-curvature estimate is inferred here. Source: MT Claim 19.43, p. 473;
`reports/2026-09-24-intrinsic-focusing-norm.md`. -/
theorem m64Intrinsic_pushed_focusing_norm_le_inv_kappa
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    {x : AnnulusCoordinates} (hx : 0 < ‖x‖) {kappa : ℝ}
    (hkappa : 0 < kappa) (hpi : kappa * ‖x‖ < Real.pi)
    (hgauss : ∀ v : AnnulusCoordinates,
      N.metric.pullbackCoefficients e x x v = inner ℝ x v) :
    N.metric.tangentNorm (e x)
        (fderiv ℝ e x
          ((Real.sin (kappa * ‖x‖) / (kappa * ‖x‖)) • x)) ≤
      kappa⁻¹ := by
  rw [m64Intrinsic_pushed_focusing_norm N e hx hkappa hpi hgauss]
  simpa only [inv_eq_one_div] using
    (div_le_div_of_nonneg_right (Real.sin_le_one (kappa * ‖x‖)) hkappa.le)

end PoincareMT
