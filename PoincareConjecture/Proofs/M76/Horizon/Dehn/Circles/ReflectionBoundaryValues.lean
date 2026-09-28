import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SinglePeriodReflectionAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusShear

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

theorem reflection_annulus_shifted_negative_boundary
    {X : Type*} {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (τ : ((ℝ × ℝ) × ℝ) → X) (g : (ℝ × ℝ) → X)
    (hend : τ ((-d, d), 2 * L) = τ ((-d, -d), 0))
    (hcurve : ∀ s ∈ Icc 0 (4 * L),
      g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d)) =
        if s ≤ 2 * L then τ ((-d, d), s) else τ ((-d, -d), s - 2 * L)) :
    ∀ s ∈ Icc 0 (4 * L),
      g (annulusMap L (by linarith) (((s + 2 * L : ℝ) : AddCircle (4 * L)), -d)) =
        if s ≤ 2 * L then τ ((-d, -d), s) else τ ((-d, d), s - 2 * L) := by
  intro s hs
  have hL : 0 < L := by linarith
  by_cases hle : s ≤ 2 * L
  · rw [if_pos hle, hcurve (s + 2 * L) ⟨by linarith [hs.1], by linarith⟩]
    by_cases hz : s = 0
    · subst s
      simpa only [zero_add, if_pos le_rfl] using hend
    · have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hz)
      rw [if_neg (by linarith), add_sub_cancel_right]
  · have ht : s - 2 * L ∈ Icc 0 (4 * L) := ⟨by linarith, by linarith [hs.2]⟩
    have hcoe : ((s + 2 * L : ℝ) : AddCircle (4 * L)) =
        ((s - 2 * L : ℝ) : AddCircle (4 * L)) := by
      have hreal : s + 2 * L = (s - 2 * L) + 4 * L := by ring
      rw [hreal, AddCircle.coe_add, AddCircle.coe_period, add_zero]
    rw [hcoe, hcurve _ ht, if_neg hle, if_pos (by linarith [hs.2])]

end Dehn
