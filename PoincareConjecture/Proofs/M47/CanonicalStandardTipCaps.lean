import PoincareConjecture.Proofs.M47.CanonicalStandardTipLocus
import PoincareConjecture.Proofs.M47.CanonicalNeckTipDistance
import PoincareConjecture.Definitions.M45ControlledSchedules

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

theorem standard_tip_locus_cap (S : RepairedControlledSchedulesData.{u})
    {theta s : ℝ} (htheta : theta < 1) (hs : s ∈ Icc 0 theta)
    {x : StandardCapSpace}
    (hdistance : ((S.cap_persistence.standard_cap.flow.metric s).edist 0 x).toReal *
      Real.sqrt ((S.cap_persistence.standard_cap.flow.connection s).scalarCurvature x) ≤
        (57 / 10 : ℝ) * S.setup.epsilon⁻¹) :
    ∃ N : CapCertificate (S.cap_persistence.standard_cap.flow.metric s),
      N.epsilon = S.calibration.beta * S.setup.epsilon / 3 ∧
      N.cap_constant ≤ S.calibration.Cstandard + 1 ∧
      N.connection = S.cap_persistence.standard_cap.flow.connection s ∧ x ∈ N.core := by
  have he := S.setup.epsilon_pos
  have hbeta := S.calibration.beta_pos
  have hbetaSmall := S.calibration.beta_lt_half
  have hsmall : S.setup.epsilon ≤ 1 / 200 :=
    S.setup.epsilon_le.trans (min_le_left _ _)
  have hgamma : S.calibration.beta * S.setup.epsilon / 3 ≤ 1 / 1200 := by
    have h := mul_le_mul hbetaSmall.le hsmall he.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith only [h]
  have hbetaInv : 2 < S.calibration.beta⁻¹ := by
    have h := mul_lt_mul_of_pos_right
      (show 2 * S.calibration.beta < 1 by linarith only [hbetaSmall]) (inv_pos.mpr hbeta)
    simpa only [mul_assoc, mul_inv_cancel₀ hbeta.ne', mul_one, one_mul] using h
  have hmargin : (57 / 10 : ℝ) * S.setup.epsilon⁻¹ <
      (19 / 20 : ℝ) * (S.calibration.beta * S.setup.epsilon / 3)⁻¹ := by
    have h := mul_lt_mul_of_pos_right hbetaInv (inv_pos.mpr he)
    have hid : (S.calibration.beta * S.setup.epsilon / 3)⁻¹ =
        3 * S.calibration.beta⁻¹ * S.setup.epsilon⁻¹ := by field_simp
    rw [hid]
    nlinarith only [h]
  have htime : s ∈ Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime := by
    rw [S.cap_persistence.standard_cap.lifetime_one]
    exact ⟨hs.1, hs.2.trans_lt htheta⟩
  obtain ⟨N⟩ := standardCanonical_cap_of_tip_distance S.cap_persistence.standard_cap
    hgamma (S.calibration.canonical_source s htime x) (hdistance.trans_lt hmargin)
  obtain ⟨refined⟩ := S.calibration.cap_refinement s x N
  exact ⟨refined.cap, refined.epsilon_eq, refined.constant_eq.le,
    refined.connection_eq, refined.contains⟩

theorem exists_compact_standard_tip_cap_cover (S : RepairedControlledSchedulesData.{u})
    {theta : ℝ} (htheta0 : 0 < theta) (htheta : theta < 1) :
    let K : Set (ℝ × StandardCapSpace) := {p | p.1 ∈ Icc 0 theta ∧
      ((S.cap_persistence.standard_cap.flow.metric p.1).edist 0 p.2).toReal *
        Real.sqrt ((S.cap_persistence.standard_cap.flow.connection p.1).scalarCurvature p.2) ≤
          (57 / 10 : ℝ) * S.setup.epsilon⁻¹}
    ∃ R : ℝ, 0 ≤ R ∧ IsCompact K ∧
      K ⊆ Icc 0 theta ×ˢ {x | S.standard_initial.metric.edist 0 x ≤ ENNReal.ofReal R} ∧
      ∀ p ∈ K, ∃ N : CapCertificate (S.cap_persistence.standard_cap.flow.metric p.1),
        N.epsilon = S.calibration.beta * S.setup.epsilon / 3 ∧
        N.cap_constant ≤ S.calibration.Cstandard + 1 ∧
        N.connection = S.cap_persistence.standard_cap.flow.connection p.1 ∧ p.2 ∈ N.core := by
  dsimp only
  obtain ⟨R, hR, hcompact, hsub⟩ := exists_compact_standard_tip_locus S.cap_persistence
    htheta0 htheta
      (mul_nonneg (show (0 : ℝ) ≤ 57 / 10 by norm_num)
        (inv_pos.mpr S.setup.epsilon_pos).le)
  refine ⟨R, hR, hcompact, hsub, ?_⟩
  intro p hp
  exact standard_tip_locus_cap S htheta hp.1 hp.2

end PoincareConjecture.Proofs.M47
