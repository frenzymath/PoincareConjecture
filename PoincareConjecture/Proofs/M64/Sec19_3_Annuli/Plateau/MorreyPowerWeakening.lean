import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace PoincareConjecture

theorem m64Morrey_power_bound_weaken
    {E K R r beta gamma : ℝ} (hE : E ≤ K * r ^ beta)
    (hK : 0 ≤ K) (hR : 0 < R) (hr : 0 < r) (hrr : r ≤ R)
    (_hgamma : 0 < gamma) (hgamma_le : gamma ≤ beta) :
    E ≤ (K * R ^ (beta - gamma)) * r ^ gamma := by
  have hR0 : 0 ≤ R := hR.le
  have hr0 : 0 ≤ r := hr.le
  have hbg : 0 ≤ beta - gamma := sub_nonneg.mpr hgamma_le
  have hpow_base : r ^ (beta - gamma) ≤ R ^ (beta - gamma) :=
    Real.rpow_le_rpow hr0 hrr hbg
  have hpow_nonneg : 0 ≤ r ^ gamma := Real.rpow_nonneg hr0 gamma
  have hpow : r ^ beta ≤ R ^ (beta - gamma) * r ^ gamma := by
    calc
      r ^ beta = r ^ (beta - gamma + gamma) := by congr 1; linarith
      _ = r ^ (beta - gamma) * r ^ gamma :=
        Real.rpow_add hr (beta - gamma) gamma
      _ ≤ R ^ (beta - gamma) * r ^ gamma :=
        mul_le_mul_of_nonneg_right hpow_base hpow_nonneg
  calc
    E ≤ K * r ^ beta := hE
    _ ≤ K * (R ^ (beta - gamma) * r ^ gamma) :=
      mul_le_mul_of_nonneg_left hpow hK
    _ = (K * R ^ (beta - gamma)) * r ^ gamma := by ring

end PoincareConjecture
