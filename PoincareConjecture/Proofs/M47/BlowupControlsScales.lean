import PoincareConjecture.Proofs.M47.FirstFailureWindow

set_option autoImplicit false

namespace PoincareConjecture.M47

theorem first_failure_blowup_scale {r Q : ℝ} (hr : 0 < r)
    (hQ : r⁻¹ ^ 2 ≤ Q) :
    0 < Q ∧ 0 < (Q * r ^ 2)⁻¹ ∧ (Q * r ^ 2)⁻¹ ≤ 1 ∧
      r⁻¹ ^ 2 / Q = (Q * r ^ 2)⁻¹ ∧
      Q⁻¹ = (Q * r ^ 2)⁻¹ * r ^ 2 := by
  have hQpos := (Proofs.M47.inverse_scalar_duration_bounds hr hQ).1
  have hprod : 0 < Q * r ^ 2 := mul_pos hQpos (sq_pos_of_pos hr)
  have hbound : 1 ≤ Q * r ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hQ (sq_nonneg r)
    have hid : r⁻¹ ^ 2 * r ^ 2 = 1 := by field_simp [hr.ne']
    rwa [hid] at h
  refine ⟨hQpos, inv_pos.mpr hprod, (inv_le_one₀ hprod).mpr hbound, ?_, ?_⟩
  · field_simp [hr.ne', hQpos.ne']
  · field_simp [hr.ne', hQpos.ne']

theorem first_failure_normalized_canonical_threshold {r Q R : ℝ}
    (hr : 0 < r) (hQ : r⁻¹ ^ 2 ≤ Q) (hR : 1 ≤ R / Q) : r⁻¹ ^ 2 ≤ R := by
  have hQpos := (Proofs.M47.inverse_scalar_duration_bounds hr hQ).1
  exact hQ.trans (by simpa only [one_mul] using (le_div_iff₀ hQpos).mp hR)

end PoincareConjecture.M47
