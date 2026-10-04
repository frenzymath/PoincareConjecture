import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry

/-!
# Monotonicity of generalized noncollapsing

The half-open backward-cylinder convention of Morgan--Tian Definition 9.1,
printed p. 179, is retained. These adapters restrict the scale range or
weaken the volume constant without changing any cylinder or slice metric.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Noncollapsing on a scale range holds on every smaller range, with
the same backward-cylinder convention. See Morgan--Tian Definition 9.1,
printed p. 179. -/
theorem GeneralizedKappaNoncollapsedAt.mono_radius
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {κ r₀ r₁ : ℝ}
    (h : GeneralizedKappaNoncollapsedAt F p κ r₀) (hr : r₁ ≤ r₀) :
    GeneralizedKappaNoncollapsedAt F p κ r₁ := by
  intro r hpos hle
  exact h r hpos (hle.trans hr)

/-- Decreasing the noncollapse constant weakens its actual volume lower
bound. See Morgan--Tian Definition 9.1, printed p. 179. -/
theorem GeneralizedKappaNoncollapsedAt.mono_kappa
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {κ κ' r₀ : ℝ}
    (h : GeneralizedKappaNoncollapsedAt F p κ r₀) (hκ : κ' ≤ κ) :
    GeneralizedKappaNoncollapsedAt F p κ' r₀ := by
  intro r hr hrr₀ hinterval e hzero hcurvature
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hκ (pow_nonneg hr.le 3))).trans
      (h r hr hrr₀ hinterval e hzero hcurvature)

end PoincareMT
