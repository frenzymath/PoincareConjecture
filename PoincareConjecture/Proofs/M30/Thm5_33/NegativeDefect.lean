import PoincareConjecture.Definitions.M28BoundedDistance
import PoincareConjecture.Proofs.M30.Mathlib.LogPinching










set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30



theorem weak_log_pinching_of_branch {F : GeneralizedRicciFlowData.{u}}
    (hF : generalizedPinchedOrNonnegative F) {t : ℝ} (ht : t ∈ F.interval)
    (x : (F.slice t).carrier)
    (hX : 0 < (F.connection t).negativeCurvaturePart x) :
    2 * (F.connection t).negativeCurvaturePart x *
        (Real.log ((F.connection t).negativeCurvaturePart x) - 3) ≤ F.scalar ⟨t, x⟩ := by
  rcases hF with hpinched | hnonnegative
  · have h := hpinched.2 t ht
    have hlog : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith [h.2.1])
    have hbound := h.2.2.2 x hX
    have hprod := mul_nonneg (show 0 ≤ 2 * (F.connection t).negativeCurvaturePart x by
      positivity) hlog
    nlinarith
  · exact (hnonnegative.2 t ht x).2 hX




theorem eventually_negativeDefect_le (S : GeneralizedBlowupSequence.{u})
    (hbranch : ∀ k, generalizedPinchedOrNonnegative (S.flow k))
    (B : ℝ) (hB : 0 ≤ B) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ k : ℕ in atTop, ∀ t, t ∈ (S.flow k).interval →
      ∀ x : ((S.flow k).slice t).carrier,
        (S.flow k).scalar ⟨t, x⟩ ≤ B * S.scale k →
        ((S.flow k).connection t).negativeCurvaturePart x ≤ eta * S.scale k := by
  filter_upwards [S.scalar_diverges.eventually_ge_atTop
    (Real.exp (B / eta + 4) / eta)] with k hk
  intro t ht x hR
  apply negative_le_scaled_of_log_pinching (S.base_scalar_pos k) hB heta
    ((div_le_iff₀ heta).mp hk |>.trans_eq (mul_comm _ _)) hR
  exact weak_log_pinching_of_branch (hbranch k) ht x

end PoincareConjecture.M30
