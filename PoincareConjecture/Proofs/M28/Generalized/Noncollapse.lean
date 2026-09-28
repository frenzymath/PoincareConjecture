import PoincareConjecture.Definitions.Ch11.BlowupLimits









set_option autoImplicit false

universe u

namespace PoincareConjecture




theorem GeneralizedKappaNoncollapsedAt.mono_radius
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {κ r₀ r₁ : ℝ}
    (h : GeneralizedKappaNoncollapsedAt F p κ r₀) (hr : r₁ ≤ r₀) :
    GeneralizedKappaNoncollapsedAt F p κ r₁ := by
  intro r hpos hle
  exact h r hpos (hle.trans hr)



theorem GeneralizedKappaNoncollapsedAt.mono_kappa
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {κ κ' r₀ : ℝ}
    (h : GeneralizedKappaNoncollapsedAt F p κ r₀) (hκ : κ' ≤ κ) :
    GeneralizedKappaNoncollapsedAt F p κ' r₀ := by
  intro r hr hrr₀ hinterval e hzero hcurvature
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hκ (pow_nonneg hr.le 3))).trans
      (h r hr hrr₀ hinterval e hzero hcurvature)

end PoincareConjecture
