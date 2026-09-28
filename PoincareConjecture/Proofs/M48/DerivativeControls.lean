import PoincareConjecture.Definitions.Ch16.ControlledSurgery

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem SurgeryScalarDerivativeControlOn.restrict
    {F : SurgeryFlowData.{u}} {J J' : Set ℝ} {r C : ℝ}
    (h : SurgeryScalarDerivativeControlOn F J r C) (hJ : J' ⊆ J) :
    SurgeryScalarDerivativeControlOn F J' r C := by
  intro a b hab hI hS x t ht hR
  exact h a b hab hI hS x t ⟨hJ ht.1, ht.2⟩ hR

theorem SurgeryScalarDerivativeControlOn.of_radius_le
    {F : SurgeryFlowData.{u}} {J : Set ℝ} {r r' C : ℝ}
    (h : SurgeryScalarDerivativeControlOn F J r C)
    (hr' : 0 < r') (hr : r' ≤ r) :
    SurgeryScalarDerivativeControlOn F J r' C := by
  have hthreshold : r⁻¹ ^ 2 ≤ (r')⁻¹ ^ 2 := by
    gcongr
    exact inv_nonneg.mpr (hr'.le.trans hr)
  intro a b hab hI hS x t ht hR
  exact h a b hab hI hS x t ht (hthreshold.trans hR)

end PoincareConjecture
