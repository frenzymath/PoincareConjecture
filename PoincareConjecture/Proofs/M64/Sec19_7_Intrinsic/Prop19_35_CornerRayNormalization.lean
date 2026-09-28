import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ComplexConeArea

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set InnerProductGeometry
open scoped ComplexConjugate

namespace PoincareConjecture

theorem m64Intrinsic_complex_corner_normalization
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hangle : angle x y ∈ Ioo (0 : ℝ) Real.pi) :
    ∃ E : ℂ ≃ₗᵢ[ℝ] ℂ, E x = (‖x‖ : ℂ) ∧
      E y = (‖y‖ : ℂ) * (Complex.cos (angle x y : ℂ) +
        Complex.sin (angle x y : ℂ) * Complex.I) := by
  let R := rotation (Circle.exp (-Complex.arg x))
  have hRx : R x = (‖x‖ : ℂ) := by
    dsimp only [R]
    rw [rotation_apply, Circle.coe_exp, Complex.ofReal_neg, neg_mul]
    calc
      Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) * x =
          Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) *
            ((‖x‖ : ℂ) * Complex.exp ((Complex.arg x : ℂ) * Complex.I)) :=
        congrArg (fun z => Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) * z)
          (Complex.norm_mul_exp_arg_mul_I x).symm
      _ = (‖x‖ : ℂ) * (Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) *
          Complex.exp ((Complex.arg x : ℂ) * Complex.I)) := by ring
      _ = (‖x‖ : ℂ) := by
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hRy : R y ≠ 0 := by
    intro h
    apply hy
    apply R.injective
    simpa only [map_zero] using h
  have harg : angle x y = |Complex.arg (R y)| := by
    calc
      angle x y = angle (R x) (R y) := (R.toLinearIsometry.angle_map x y).symm
      _ = angle (1 : ℂ) (R y) := by
        rw [hRx]
        simpa only [Complex.real_smul, mul_one] using
          angle_smul_left_of_pos (1 : ℂ) (R y) (norm_pos_iff.mpr hx)
      _ = |Complex.arg (R y)| := Complex.angle_one_left hRy
  by_cases hnonneg : 0 ≤ Complex.arg (R y)
  · refine ⟨R, hRx, ?_⟩
    rw [harg, abs_of_nonneg hnonneg]
    simpa only [R.norm_map] using (Complex.norm_mul_cos_add_sin_mul_I (R y)).symm
  · let E := R.trans Complex.conjLIE
    have hEx : E x = (‖x‖ : ℂ) := by
      change conj (R x) = (‖x‖ : ℂ)
      rw [hRx, Complex.conj_ofReal]
    have hnepi : Complex.arg (R y) ≠ Real.pi := by
      intro h
      rw [h, abs_of_pos Real.pi_pos] at harg
      exact hangle.2.ne harg
    have hEarg : Complex.arg (E y) = angle x y := by
      change Complex.arg (conj (R y)) = angle x y
      rw [Complex.arg_conj, if_neg hnepi, harg, abs_of_neg (lt_of_not_ge hnonneg)]
    refine ⟨E, hEx, ?_⟩
    simpa only [E.norm_map, hEarg] using (Complex.norm_mul_cos_add_sin_mul_I (E y)).symm

end PoincareConjecture
