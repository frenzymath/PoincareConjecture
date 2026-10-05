import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.Round.Metric
import PoincareLib.Geometry.Riemannian.Measure.Green.CompactSupport

/-!
# Integrating a smooth round Laplacian

Morgan-Tian Claim 18.12, printed pp. 426-427. M07's actual Green
identity with the constant test function gives a zero integral for
the Laplacian of every smooth function on the closed round sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT

/-- A smooth round-sphere Laplacian is genuinely integrable and has
zero integral. Source: MT Claim 18.12, pp. 426-427, regularized curvature
derivation using the actual Green identity. -/
theorem m60RoundSphere_integral_laplacian (D : LeviCivitaData m60RoundSphereMetric)
    (φ : UnitTwoSphere → ℝ) (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ) :
    Integrable (D.laplacian φ) m60RoundSphereMetric.volumeMeasure ∧
      (∫ p, D.laplacian φ p ∂m60RoundSphereMetric.volumeMeasure) = 0 := by
  have hi := D.integrable_mul_laplacian (contMDiff_const (c := (1 : ℝ))) hφ
    (HasCompactSupport.of_compactSpace _)
  have hg := D.integral_mul_laplacian_of_sigmaCompact (contMDiff_const (c := (1 : ℝ))) hφ
    (HasCompactSupport.of_compactSpace _)
  have hgrad (p : UnitTwoSphere) : D.gradient (fun _ => (1 : ℝ)) p = 0 := by
    simp [LeviCivitaData.gradient, mvfderiv_const]
  simp only [one_mul] at hi hg
  refine ⟨hi, ?_⟩
  simpa only [hgrad, map_zero, zero_apply, integral_zero, neg_zero] using hg

end PoincareMT
