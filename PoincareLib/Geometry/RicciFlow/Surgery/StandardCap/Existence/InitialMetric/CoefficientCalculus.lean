import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Connection

/-!
# Radial metric and connection coefficients in terms of the profile

Morgan-Tian Lemma 12.2, printed pp. 294-295. Differentiating the explicit
metric coefficients reduces the actual connection to rational functions
of the arclength profile and its slope. All identities here exclude the
singular radius and explicitly require a nonzero profile when dividing
by it. See the M34 radial-curvature derivation.
-/

set_option autoImplicit false

open Filter
open scoped Topology ContDiff

namespace PoincareMT.M34

/-- Radial derivative of the angular metric coefficient
(Lemma 12.2 curvature computation, pp. 294-295). -/
theorem capAngularCoefficient_hasDerivAt (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (capAngularCoefficient a)
      (2 * capProfile a r * (r * capSlope a r - capProfile a r) / r ^ 3) r := by
  have he : capAngularCoefficient a =ᶠ[𝓝 r] (fun s => (capProfile a s / s) ^ 2) := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact if_neg hs
  have h := ((capProfile_hasDerivAt a r).div (hasDerivAt_id r) hr).pow 2
  convert! h.congr_of_eventuallyEq he using 1
  simp only [Pi.div_apply, id_eq, Nat.reduceSub, pow_one]
  field_simp
  ring

/-- Radial derivative of the rank-one metric correction
(Lemma 12.2 curvature computation, pp. 294-295). -/
theorem capRadialCoefficient_hasDerivAt (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (capRadialCoefficient a)
      ((-2 * r ^ 2 - 2 * r * capProfile a r * capSlope a r +
        4 * capProfile a r ^ 2) / r ^ 5) r := by
  have he : capRadialCoefficient a =ᶠ[𝓝 r]
      (fun s => (1 - capAngularCoefficient a s) / s ^ 2) := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact if_neg hs
  convert! (((capAngularCoefficient_hasDerivAt a hr).const_sub 1).div
    ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)).congr_of_eventuallyEq he using 1
  rw [capAngularCoefficient, if_neg hr]
  simp only [Pi.pow_apply, id_eq]
  field_simp
  ring

/-- The first Christoffel coefficient uses only the profile and its
slope (Lemma 12.2 curvature computation, pp. 294-295). -/
theorem capChristoffelA_eq (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    capChristoffelA a r = capSlope a r / (r * capProfile a r) - 1 / r ^ 2 := by
  rw [capChristoffelA, (capAngularCoefficient_hasDerivAt a hr).deriv,
    capAngularCoefficient, if_neg hr]
  field_simp

/-- The second Christoffel coefficient uses only the profile and its
slope (Lemma 12.2 curvature computation, pp. 294-295). -/
theorem capChristoffelB_eq (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    capChristoffelB a r = 1 / r ^ 2 - capProfile a r * capSlope a r / r ^ 3 := by
  rw [capChristoffelB, (capAngularCoefficient_hasDerivAt a hr).deriv,
    capRadialCoefficient, if_neg hr, capAngularCoefficient, if_neg hr]
  field_simp
  ring

/-- The radial-geodesic identity fixes the third Christoffel coefficient
(Lemma 12.2 curvature computation, pp. 294-295). -/
theorem capChristoffelC_eq (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    capChristoffelC a r = -(2 * capChristoffelA a r + capChristoffelB a r) / r ^ 2 := by
  rw [capChristoffelC, (capRadialCoefficient_hasDerivAt a hr).deriv,
    capChristoffelA_eq a hr hf, capChristoffelB_eq a hr,
    capRadialCoefficient, if_neg hr, capAngularCoefficient, if_neg hr]
  field_simp
  ring

/-- Cartesian radial lines are geodesic at every nonzero radius
(Lemma 12.2 curvature computation, pp. 294-295). -/
theorem capChristoffel_radial_identity (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    2 * capChristoffelA a r + capChristoffelB a r + capChristoffelC a r * r ^ 2 = 0 := by
  rw [capChristoffelC_eq a hr hf, div_mul_cancel₀ _ (pow_ne_zero 2 hr)]
  ring

end PoincareMT.M34
