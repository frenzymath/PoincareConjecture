import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.EarlyBallVolume
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.LateBallVolume










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M34



theorem standardFlow_noncollapsingCertificate {g0 : StandardInitialMetric}
    (F : MaximalStandardCapFlow g0) (P : M34StandardCapPredecessors) :
    Nonempty (StandardFlowNoncollapsingCertificate F) := by
  have hhalf : F.base.lifetime / 2 ∈ Ico 0 F.base.lifetime := by
    constructor <;> linarith [F.base.lifetime_pos]
  obtain ⟨rEarly, kEarly, hrEarly, hkEarly, hEarly⟩ :=
    partialFlow_early_small_ball_volume F.base P.curvature hhalf
  obtain ⟨kLate, hkLate, hLate⟩ := partialFlow_late_small_ball_volume F.base P
  have hsqrt : 0 < Real.sqrt (F.base.lifetime / 8) :=
    Real.sqrt_pos.mpr (by linarith [F.base.lifetime_pos])
  refine ⟨{
    radius := min rEarly (Real.sqrt (F.base.lifetime / 8))
    radius_pos := lt_min hrEarly hsqrt
    kappa := min kEarly kLate
    kappa_pos := lt_min hkEarly hkLate
    bound := ?_
  }⟩
  intro t ht p r hr hr0 _ hcurv
  by_cases htime : t ≤ F.base.lifetime / 2
  · calc
      ENNReal.ofReal (min kEarly kLate * r ^ 3) ≤ ENNReal.ofReal (kEarly * r ^ 3) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hr.le _))
      _ ≤ _ := hEarly t ⟨ht.1, htime⟩ p r hr (hr0.trans (min_le_left _ _))
  · calc
      ENNReal.ofReal (min kEarly kLate * r ^ 3) ≤ ENNReal.ofReal (kLate * r ^ 3) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hr.le _))
      _ ≤ _ := hLate t ⟨(lt_of_not_ge htime).le, ht.2⟩ p r hr
        (hr0.trans (min_le_right _ _)) hcurv

end PoincareConjecture.M34
