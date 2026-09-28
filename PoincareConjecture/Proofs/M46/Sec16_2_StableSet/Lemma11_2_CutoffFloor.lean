import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CapBirth










set_option autoImplicit false

namespace PoincareConjecture.Proofs.M46



noncomputable def capScalarCutoff (epsilon c r : ℝ) : ℝ :=
  min 1 (r * min 1 c / (8 * epsilon))


theorem capScalarCutoff_pos {epsilon c r : ℝ}
    (he : 0 < epsilon) (hc : 0 < c) (hr : 0 < r) :
    0 < capScalarCutoff epsilon c r := by
  unfold capScalarCutoff
  exact lt_min zero_lt_one (div_pos (mul_pos hr (lt_min zero_lt_one hc))
    (mul_pos (by norm_num) he))



theorem cap_birth_floor_gt_four_inv_sq
    (F : SurgeryFlowData) {t c r : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hr : 0 < r)
    (hdelta : F.parameters.delta t ≤ capScalarCutoff F.parameters.epsilon c r) :
    4 * r⁻¹ ^ 2 < c / (2 * (F.parameters.h t) ^ 2) := by
  let m := min 1 c
  have hmpos : 0 < m := lt_min zero_lt_one hc
  have hmone : m ≤ 1 := min_le_left _ _
  have hmc : m ≤ c := min_le_right _ _
  have hdeltaPos := F.parameters.delta_pos t ht
  have hdeltaOne : F.parameters.delta t ≤ 1 := hdelta.trans (min_le_left _ _)
  have hdeltaSmall : F.parameters.delta t ≤ r * m / (8 * F.parameters.epsilon) :=
    hdelta.trans (min_le_right _ _)
  have hdeltaSq : F.parameters.delta t ^ 2 ≤ F.parameters.delta t := by
    nlinarith [mul_nonneg hdeltaPos.le (sub_nonneg.mpr hdeltaOne)]
  have hhe : F.parameters.h t ≤ F.parameters.delta t * F.parameters.epsilon := by
    exact ((F.parameters.h_le t ht).trans
      (mul_le_mul_of_nonneg_left (F.parameters.r_le_epsilon t ht) (sq_nonneg _))).trans
        (mul_le_mul_of_nonneg_right hdeltaSq F.parameters.epsilon_pos.le)
  have hscale := (le_div_iff₀
    (mul_pos (by norm_num : (0 : ℝ) < 8) F.parameters.epsilon_pos)).mp hdeltaSmall
  have hheight : 8 * F.parameters.h t ≤ r * m := by nlinarith
  have hheightPos := F.parameters.h_pos t ht
  have hsquare : 64 * (F.parameters.h t) ^ 2 ≤ r ^ 2 * m ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hheight)
      (by positivity : 0 ≤ r * m + 8 * F.parameters.h t)
    nlinarith
  have hmsquare : m ^ 2 ≤ c := by
    nlinarith [mul_nonneg hmpos.le (sub_nonneg.mpr hmone)]
  have hbound := mul_le_mul_of_nonneg_left hmsquare (sq_nonneg r)
  have hstrict : 8 * (F.parameters.h t) ^ 2 < c * r ^ 2 := by
    nlinarith [mul_pos hc (sq_pos_of_pos hr)]
  apply (lt_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hheightPos))).mpr
  apply (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos hr)).mp
  calc
    (4 * r⁻¹ ^ 2 * (2 * (F.parameters.h t) ^ 2)) * r ^ 2 =
        8 * (F.parameters.h t) ^ 2 := by field_simp [hr.ne']; norm_num
    _ < c * r ^ 2 := hstrict

end PoincareConjecture.Proofs.M46
