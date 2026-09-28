import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients










set_option autoImplicit false

open Filter
open scoped Topology

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem MemLp.smul_cutoff {u : X → E} (hu : MemLp u 2 mu)
    {theta : X → ℝ} (htheta : AEStronglyMeasurable theta mu)
    (hbound : ∀ᵐ x ∂mu, |theta x| ≤ 1) : MemLp (fun x => theta x • u x) 2 mu := by
  refine hu.of_le (htheta.smul hu.1) ?_
  filter_upwards [hbound] with x hx
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) hx




theorem Lp.norm_sub_cutoff_sq_le [IsFiniteMeasure mu] (u : Lp E 2 mu)
    {theta : X → ℝ} (htheta : AEStronglyMeasurable theta mu)
    (hbound : ∀ᵐ x ∂mu, |theta x| ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ᵐ x ∂mu, ‖u x‖ ≤ C) :
    ‖u - ((Lp.memLp u).smul_cutoff htheta hbound).toLp (fun x => theta x • u x)‖ ^ 2 ≤
      C ^ 2 * ∫ x, (1 - theta x) ^ 2 ∂mu := by
  let cut : Lp E 2 mu :=
    ((Lp.memLp u).smul_cutoff htheta hbound).toLp (fun x => theta x • u x)
  have hscalar : MemLp (fun x => 1 - theta x) 2 mu := by
    apply MemLp.of_bound (aestronglyMeasurable_const.sub htheta) 2
    filter_upwards [hbound] with x hx
    calc
      ‖1 - theta x‖ ≤ ‖(1 : ℝ)‖ + ‖theta x‖ := norm_sub_le _ _
      _ ≤ 2 := by
        simp only [Real.norm_eq_abs, abs_one]
        linarith
  have hcut : cut =ᵐ[mu] fun x => theta x • u x := MemLp.coeFn_toLp _
  have herror := (Lp.memLp (u - cut)).norm.integrable_sq
  have hmajorant := hscalar.integrable_sq.const_mul (C ^ 2)
  have hpoint : ∀ᵐ x ∂mu, ‖(u - cut) x‖ ^ 2 ≤ C ^ 2 * (1 - theta x) ^ 2 := by
    filter_upwards [Lp.coeFn_sub u cut, hcut, hu] with x hsub hc hux
    rw [hsub, Pi.sub_apply, hc]
    have heq : u x - theta x • u x = (1 - theta x) • u x := by
      rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) hC).mpr hux) (sq_nonneg _)).trans_eq (mul_comm _ _)
  change ‖u - cut‖ ^ 2 ≤ _
  rw [Lp.norm_sq_eq_integral_norm_sq, ← integral_const_mul]
  exact integral_mono_ae herror hmajorant hpoint

end MeasureTheory
