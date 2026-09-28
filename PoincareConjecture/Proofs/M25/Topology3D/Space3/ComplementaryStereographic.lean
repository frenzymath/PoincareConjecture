import PoincareConjecture.Proofs.M25.Topology3D.Space3.StereographicCap

set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem stereographicCapHeight_mem_unit_interval {r : ℝ} (hr : 0 < r) :
    stereographicCapHeight r ∈ Ioo (-1 : ℝ) 1 := by
  have hd : 0 < 4 + r ^ 2 := by positivity
  constructor
  · change -1 < (4 - r ^ 2) / (4 + r ^ 2)
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  · change (4 - r ^ 2) / (4 + r ^ 2) < 1
    apply (div_lt_one hd).mpr
    nlinarith [sq_pos_of_pos hr]

theorem stereographicCapHeight_complement {r : ℝ} (hr : 0 < r) :
    stereographicCapHeight (4 / r) = -stereographicCapHeight r := by
  have hd : 4 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hD : 4 + (4 / r) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold stereographicCapHeight
  field_simp [hr.ne', hd, hD]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem stereoInvFun_image_closedBall_pos (v : E) (hv : ‖v‖ = 1) {r : ℝ}
    (hr : 0 < r) :
    (fun w => (stereoInvFun hv w : E)) '' closedBall 0 r =
      {y : E | ‖y‖ = 1 ∧ stereographicCapHeight r ≤ ⟪-v, y⟫_ℝ} := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨norm_eq_of_mem_sphere _, (stereoInvFun_cap_iff v hv hr.le w).mpr hw⟩
  · rintro ⟨hynorm, hycap⟩
    have hyv : y ≠ v := by
      intro heq
      rw [heq, inner_neg_left, real_inner_self_eq_norm_sq, hv] at hycap
      have ha := (stereographicCapHeight_mem_unit_interval hr).1
      norm_num at hycap
      linarith
    let q : sphere (0 : E) 1 := ⟨y, mem_sphere_zero_iff_norm.mpr hynorm⟩
    have heq : (stereoInvFun hv (stereoToFun v y) : E) = y :=
      congrArg Subtype.val (stereo_left_inv hv (x := q) hyv)
    refine ⟨stereoToFun v y, ?_, heq⟩
    apply (stereoInvFun_cap_iff v hv hr.le _).mp
    rwa [heq]

theorem stereoInvFun_cap_eq_iff (v : E) (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (w : (ℝ ∙ v)ᗮ) :
    stereographicCapHeight r = ⟪-v, (stereoInvFun hv w : E)⟫_ℝ ↔ w ∈ sphere 0 r := by
  rw [stereoInvFun_opposite_height, mem_sphere_zero_iff_norm]
  have hd : 4 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hw : 4 + ‖w‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold stereographicCapHeight
  rw [div_eq_div_iff hd hw]
  constructor
  · intro h
    nlinarith [norm_nonneg w]
  · intro h
    rw [h]

theorem stereoInvFun_image_sphere_pos (v : E) (hv : ‖v‖ = 1) {r : ℝ}
    (hr : 0 < r) :
    (fun w => (stereoInvFun hv w : E)) '' sphere 0 r =
      {y : E | ‖y‖ = 1 ∧ stereographicCapHeight r = ⟪-v, y⟫_ℝ} := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨norm_eq_of_mem_sphere _, (stereoInvFun_cap_eq_iff v hv hr.le w).mpr hw⟩
  · rintro ⟨hynorm, hycap⟩
    have hyclosed : y ∈ (fun w => (stereoInvFun hv w : E)) '' closedBall 0 r := by
      rw [stereoInvFun_image_closedBall_pos v hv hr]
      exact ⟨hynorm, hycap.le⟩
    obtain ⟨w, _, rfl⟩ := hyclosed
    exact ⟨w, (stereoInvFun_cap_eq_iff v hv hr.le w).mp hycap, rfl⟩

end PoincareConjecture.M25.Topology3D
