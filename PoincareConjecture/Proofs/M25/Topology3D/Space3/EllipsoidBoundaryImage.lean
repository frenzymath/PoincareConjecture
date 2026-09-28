import PoincareConjecture.Proofs.M25.Topology3D.Space3.EllipsoidRounding

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ellipsoidRoundingTrack_one (A : E ≃L[ℝ] E) {y : E} (hy : y ≠ 0) :
    ellipsoidRoundingTrack A 1 y = ellipsoidRadialRatio A y • y := by
  rw [ellipsoidRoundingTrack, one_mul, Real.exp_log (ellipsoidRadialRatio_pos A hy)]

theorem ellipsoidRoundingTrack_image_sphere (A : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r) :
    ellipsoidRoundingTrack A 1 '' (A '' sphere (0 : E) r) = sphere 0 r := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    have hxnorm := mem_sphere_zero_iff_norm.mp hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hxnorm.trans_ne hr.ne')
    rw [mem_sphere_zero_iff_norm,
      ellipsoidRoundingTrack_one_norm A (y := A x) (A.map_ne_zero_iff.mpr hx0),
      A.symm_apply_apply]
    exact hxnorm
  · intro hz
    have hznorm := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hznorm.trans_ne hr.ne')
    have hn : 0 < ‖A.symm z‖ := norm_pos_iff.mpr (A.symm.map_ne_zero_iff.mpr hz0)
    let a := r / ‖A.symm z‖
    have ha : 0 < a := div_pos hr hn
    refine ⟨a • z, ⟨A.symm (a • z), ?_, A.apply_symm_apply _⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      exact div_mul_cancel₀ r hn.ne'
    · rw [ellipsoidRoundingTrack_one A (smul_ne_zero ha.ne' hz0),
        ellipsoidRadialRatio_smul A ha, smul_smul]
      have hcancel : ellipsoidRadialRatio A z * a = 1 := by
        dsimp [ellipsoidRadialRatio, a]
        rw [hznorm]
        field_simp
      rw [hcancel, one_smul]

end PoincareConjecture.M25.Topology3D
