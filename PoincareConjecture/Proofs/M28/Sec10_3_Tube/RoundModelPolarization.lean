import PoincareConjecture.Proofs.M13.CurvatureMultilinear

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace PoincareConjecture.M28.tube

section Algebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def roundModelGramForm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun := fun b =>
        { toFun := fun c => (B a c) • B b - (B b c) • B a
          map_add' := by
            intro c d
            ext z
            simp only [map_add, LinearMap.sub_apply, LinearMap.smul_apply,
              LinearMap.add_apply, smul_eq_mul]
            ring
          map_smul' := by
            intro r c
            ext z
            simp only [map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
              smul_eq_mul, RingHom.id_apply]
            ring }
      map_add' := by
        intro b c
        ext d z
        simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
        ring
      map_smul' := by
        intro r b
        ext d z
        simp only [map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
          LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' := by
    intro a b
    ext c d z
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    ring
  map_smul' := by
    intro r a
    ext b c d
    simp only [map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end Algebra

theorem roundModel_form_zero_of_unit_planes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hfirst : ∀ a b c d, T a b c d = -T b a c d)
    (hpair : ∀ a b c d, T a b c d = T c d a b)
    (hcyclic : ∀ a b c d, T a b c d + T b c a d + T c a b d = 0)
    (hunit : ∀ a b, ‖a‖ = 1 → ‖b‖ = 1 → inner ℝ a b = 0 → T a b a b = 0)
    (a b c d : E) : T a b c d = 0 := by
  have hlast (u v w z : E) : T u v w z = -T u v z w := by
    rw [hpair u v w z, hfirst w z u v, hpair z w u v]
  have hfirst0 (u v w : E) : T u u v w = 0 := by
    linarith only [hfirst u u v w]
  have hlast0 (u v w : E) : T u v w w = 0 := by
    linarith only [hlast u v w w]
  have horth (u v : E) (huv : inner ℝ u v = 0) : T u v u v = 0 := by
    by_cases hu : u = 0
    · simp [hu]
    by_cases hv : v = 0
    · simp [hv]
    have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hn := hunit (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)
      (by simp [norm_smul, norm_inv, hnu])
      (by simp [norm_smul, norm_inv, hnv])
      (by simp [inner_smul_left, inner_smul_right, huv])
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hn
    simpa [mul_eq_zero, hnu, hnv] using hn
  have hdiag (u v : E) : T u v u v = 0 := by
    by_cases hu : u = 0
    · simp [hu]
    have hnu : inner ℝ u u ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hu)
    let r : ℝ := inner ℝ u v / inner ℝ u u
    have hperp : inner ℝ u (v - r • u) = 0 := by
      simp only [inner_sub_right, real_inner_smul_right, r,
        div_mul_cancel₀ _ hnu, sub_self]
    have hz := horth u (v - r • u) hperp
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hfirst0, hlast0, mul_zero, sub_zero] at hz
    exact hz
  have hrepeat (u v w : E) : T u v u w = 0 := by
    have h := hdiag u (v + w)
    simp only [map_add, LinearMap.add_apply, hdiag] at h
    rw [hpair u w u v] at h
    linarith only [h]
  have hpolar (u v w z : E) : T u v w z + T w v u z = 0 := by
    have h := hrepeat (u + w) v z
    simpa only [map_add, LinearMap.add_apply, hrepeat, zero_add, add_zero,
      add_comm] using h
  have hp1 := hpolar a b c d
  have hp2 := hpolar b c a d
  have hs1 := hfirst c b a d
  have hs2 := hfirst a c b d
  have hc := hcyclic a b c d
  linarith only [hp1, hp2, hs1, hs2, hc]

end PoincareConjecture.M28.tube
