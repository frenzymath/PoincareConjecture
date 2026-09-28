import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReferenceConeArea
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory InnerProductGeometry
open scoped ENNReal Topology

namespace PoincareConjecture





theorem m64Intrinsic_complex_reference_angle
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) Real.pi) :
    angle (1 : ℂ) ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I) = a := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hne : (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re, mul_one, zero_mul, add_zero, zero_add,
      Complex.zero_im] at hi
    exact hsin.ne' hi
  have harg : Complex.arg ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I) = a := by
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      (Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos, ha.1], ha.2.le⟩)
  rw [Complex.angle_one_left hne, harg, abs_of_pos ha.1]





theorem m64Intrinsic_complex_reference_cone_volume
    {R a : ℝ} (hR : 0 < R) (ha : a ∈ Ioo (0 : ℝ) Real.pi) :
    volume {z : ℂ | ‖z‖ < R ∧ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
      z = (s : ℂ) + (t : ℂ) * ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I)} =
        ENNReal.ofReal (R ^ 2 / 2) * ENNReal.ofReal a := by
  have hnorm (z : ℂ) : ‖z‖ < R ↔ z.re ^ 2 + z.im ^ 2 < R ^ 2 := by
    have hsquare : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq z).symm
    constructor <;> intro h
    · rw [← hsquare]
      nlinarith [norm_nonneg z]
    · rw [← hsquare] at h
      nlinarith [norm_nonneg z]
  have hcone (z : ℂ) :
      (∃ s t : ℝ, 0 < s ∧ 0 < t ∧
        z = (s : ℂ) + (t : ℂ) * ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I)) ↔
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
        (z.re, z.im) = (s + t * Real.cos a, t * Real.sin a) := by
    constructor
    · rintro ⟨s, t, hs, ht, rfl⟩
      refine ⟨s, t, hs, ht, ?_⟩
      apply Prod.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
    · rintro ⟨s, t, hs, ht, heq⟩
      refine ⟨s, t, hs, ht, ?_⟩
      apply Complex.ext
      · simpa only [Complex.add_re, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero] using
          congrArg Prod.fst heq
      · simpa only [Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero] using
          congrArg Prod.snd heq
  have hset : {z : ℂ | ‖z‖ < R ∧ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
      z = (s : ℂ) + (t : ℂ) * ((Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I)} =
      Complex.measurableEquivRealProd ⁻¹' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2 ∧
        ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ p = (s + t * Real.cos a, t * Real.sin a)} := by
    ext z
    change (_ ∧ _) ↔ (z.re ^ 2 + z.im ^ 2 < R ^ 2 ∧ _)
    rw [hnorm, hcone]
    rfl
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  exact m64Intrinsic_reference_positive_cone_volume hR ha

end PoincareConjecture
