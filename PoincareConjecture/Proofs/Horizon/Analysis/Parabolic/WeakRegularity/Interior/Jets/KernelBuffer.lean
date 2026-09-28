




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.MollifiedForcingBounds
import Mathlib.Topology.MetricSpace.Thickening









open Set MeasureTheory Filter
open Poincare.Analysis.Convolution
open scoped Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

theorem exists_uniform_translated_rescaledKernel_support_subset
    {n : ℕ} {K U : Set (Spacetime n)} {ρ : Spacetime n → ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hρc : HasCompactSupport ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r ≤ ε → ∀ z ∈ K,
      tsupport (translatedKernel (rescaledKernel ρ r) z) ⊆ U := by
  obtain ⟨R, hRpos, hR⟩ := hρc.isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ / R, div_pos hδ hRpos, ?_⟩
  intro r hr hrδ z hz
  have hs : tsupport (translatedKernel (rescaledKernel ρ r) z) ⊆
      {y | ‖z - y‖ ≤ r * R} := by
    apply closure_minimal _
      (isClosed_le (continuous_const.sub continuous_id).norm continuous_const)
    intro y hy
    have hρy : ρ (r⁻¹ • (z - y)) ≠ 0 := by
      intro he
      exact hy (by simp [translatedKernel, rescaledKernel, he])
    have hb := hR _ (subset_tsupport ρ hρy)
    have hn : ‖r⁻¹ • (z - y)‖ = r⁻¹ * ‖z - y‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [hn] at hb
    have hm := mul_le_mul_of_nonneg_left hb hr.le
    simpa [← mul_assoc, hr.ne'] using hm
  intro y hy
  apply hδU
  apply Metric.mem_cthickening_of_dist_le y z δ K hz
  rw [dist_eq_norm, norm_sub_rev]
  exact (hs hy).trans ((le_div_iff₀ hRpos).mp hrδ)

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
