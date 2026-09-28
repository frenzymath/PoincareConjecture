import PoincareConjecture.Proofs.M44.Mathlib.SectionalPolarization










set_option autoImplicit false

namespace PoincareConjecture.M44

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]




theorem exists_orthonormal_curvature_quotient
    (R : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (u v : E) (hgram : 0 < inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) :
    ∃ p q : E, inner ℝ p p = 1 ∧ inner ℝ q q = 1 ∧ inner ℝ p q = 0 ∧
      R p q p q = R u v u v /
        (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) := by
  have hu : u ≠ 0 := by
    intro hu
    simp only [hu, inner_zero_left, zero_mul, zero_pow (by decide : 2 ≠ 0),
      sub_zero, lt_self_iff_false] at hgram
  have huu : 0 < inner ℝ u u := real_inner_self_pos.mpr hu
  let c := inner ℝ u v / inner ℝ u u
  let w := v - c • u
  have huw : inner ℝ u w = 0 := by
    dsimp [w, c]
    rw [inner_sub_right, real_inner_smul_right, div_mul_cancel₀ _ huu.ne', sub_self]
  have hgram_eq : inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2 =
      inner ℝ u u * inner ℝ w w := by
    dsimp [w]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    dsimp [c]
    rw [real_inner_comm v u]
    field_simp [huu.ne']
    ring
  have hww : 0 < inner ℝ w w :=
    (mul_pos_iff_of_pos_left huu).mp (hgram_eq ▸ hgram)
  have hw : w ≠ 0 := real_inner_self_pos.mp hww
  let p := ‖u‖⁻¹ • u
  let q := ‖w‖⁻¹ • w
  have hp : ‖p‖ = 1 := norm_smul_inv_norm hu
  have hq : ‖q‖ = 1 := norm_smul_inv_norm hw
  have hzero1 (a b d : E) : R a a b d = 0 := by linarith only [hfirst a a b d]
  have hzero2 (a b d : E) : R a b d d = 0 := by linarith only [hlast a b d d]
  have hplane : R u w u w = R u v u v := by
    simp only [w, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hzero1, hzero2, mul_zero, sub_zero]
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · rw [real_inner_self_eq_norm_sq, hp, one_pow]
  · rw [real_inner_self_eq_norm_sq, hq, one_pow]
  · simp only [p, q, real_inner_smul_left, real_inner_smul_right, huw, mul_zero]
  · simp only [p, q, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hplane, hgram_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    field_simp

end PoincareConjecture.M44
