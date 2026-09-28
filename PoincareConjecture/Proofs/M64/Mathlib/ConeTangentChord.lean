import PoincareConjecture.Proofs.M64.Mathlib.ClosedConeChord
import Mathlib.Topology.Order.LeftRightNhds










set_option autoImplicit false

open Set Filter
open scoped Topology





theorem m64ClosedCone_tangent_mem_and_neg_mem_of_chord_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    (C : ConvexCone ℝ E) (hC : IsClosed (C : Set E)) (hzero : (0 : E) ∈ C)
    {x y : ℝ → E} {w : E}
    (hlimit : Tendsto (fun r => r⁻¹ • y r) (𝓝[>] 0) (𝓝 w))
    (hdata : ∀ theta : ℝ, 1 < theta → ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ r : ℝ, 0 < r → r < epsilon →
        x r ∈ C ∧ y r ∈ C ∧ ‖x r‖ ≤ theta * r ∧ ‖y r‖ ≤ theta * r ∧
          2 * r ≤ theta * ‖y r - x r‖) : w ∈ C ∧ -w ∈ C := by
  have hw : ‖w‖ ≤ 1 := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro theta htheta
    obtain ⟨epsilon, hepsilon, hbound⟩ := hdata theta htheta
    apply le_of_tendsto hlimit.norm
    filter_upwards [Ioo_mem_nhdsGT hepsilon] with r hr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr.1), ← div_eq_inv_mul]
    exact (div_le_iff₀ hr.1).mpr (hbound r hr.1 hr.2).2.2.2.1
  have hwC : w ∈ C := by
    obtain ⟨epsilon, hepsilon, hbound⟩ := hdata 2 (by norm_num)
    apply hC.mem_of_tendsto hlimit
    filter_upwards [Ioo_mem_nhdsGT hepsilon] with r hr
    exact C.smul_mem (inv_pos.mpr hr.1) (hbound r hr.1 hr.2).2.1
  refine ⟨hwC, ?_⟩
  by_contra hopp
  obtain ⟨d, _, hd2, hchord⟩ :=
    m64ClosedCone_exists_scaled_chord_bound_to_vector C hC hzero hw hopp
  have hthetaNear : ∀ᶠ theta : ℝ in 𝓝[>] 1, theta * (theta * d + theta - 1) < 2 := by
    have hf : ContinuousAt (fun theta : ℝ => theta * (theta * d + theta - 1)) 1 := by
      fun_prop
    exact (hf.eventually (gt_mem_nhds (by simpa using hd2))).filter_mono nhdsWithin_le_nhds
  obtain ⟨theta, hthetaBound, htheta⟩ := (hthetaNear.and self_mem_nhdsWithin).exists
  have htpos : 0 < theta := zero_lt_one.trans htheta
  obtain ⟨epsilon, hepsilon, hbound⟩ := hdata theta htheta
  have hlim := ((hlimit.sub_const (theta • w)).norm.const_add (theta * d)).const_mul theta
  have htwo : 2 ≤ theta * (theta * d + ‖w - theta • w‖) := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hepsilon] with r hr
    obtain ⟨hx, _, hxn, _, hlower⟩ := hbound r hr.1 hr.2
    have hdist := hchord (theta * r) (mul_pos htpos hr.1) (x r) hx hxn
    have hrescale : r • (r⁻¹ • y r - theta • w) = y r - (theta * r) • w := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.1.ne', one_smul, smul_smul, mul_comm r theta]
    have hnorm : ‖y r - (theta * r) • w‖ = r * ‖r⁻¹ • y r - theta • w‖ := by
      rw [← hrescale, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
    have htriangle : ‖y r - x r‖ ≤
        (theta * r) * d + r * ‖r⁻¹ • y r - theta • w‖ := by
      calc
        ‖y r - x r‖ ≤ ‖y r - (theta * r) • w‖ + ‖(theta * r) • w - x r‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (theta * r) * d + r * ‖r⁻¹ • y r - theta • w‖ := by
          rw [hnorm]
          linarith
    have hh := hlower.trans (mul_le_mul_of_nonneg_left htriangle htpos.le)
    have halg : theta * ((theta * r) * d + r * ‖r⁻¹ • y r - theta • w‖) =
        (theta * (theta * d + ‖r⁻¹ • y r - theta • w‖)) * r := by ring
    rw [halg] at hh
    exact (mul_le_mul_iff_left₀ hr.1).mp hh
  have herr : ‖w - theta • w‖ ≤ theta - 1 := by
    rw [show w - theta • w = (1 - theta) • w by module, norm_smul, Real.norm_eq_abs,
      abs_of_neg (sub_neg.mpr htheta)]
    nlinarith [mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr htheta.le)]
  have hfinal : theta * (theta * d + ‖w - theta • w‖) < 2 := calc
    theta * (theta * d + ‖w - theta • w‖) ≤ theta * (theta * d + theta - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) htpos.le
    _ < 2 := hthetaBound
  exact (not_lt_of_ge htwo) hfinal
