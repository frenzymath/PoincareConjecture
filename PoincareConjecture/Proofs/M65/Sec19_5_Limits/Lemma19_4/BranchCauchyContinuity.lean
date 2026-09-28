import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchRegularizedOperator
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchKernelError
import Mathlib.Topology.UniformSpace.UniformApproximation










set_option autoImplicit false

open Set MeasureTheory Metric Filter
open scoped Topology

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]




theorem norm_sub_regularizedCauchyOperator_le {h : ℂ → E} {δ R B : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ w, ‖h w‖ ≤ B) (z : ℂ) :
    ‖cauchyOperator h z - regularizedCauchyOperator δ h z‖ ≤ 4 * δ * B := by
  have h0 := integrable_cauchyOperator_of_bound hh hs hb z
  have h1 := integrable_regularizedCauchyOperator hδ hh hs hb z
  have hk := kernelError_integrable_bound hδ z
  have hi : Integrable
      (fun w : ℂ => ((z - w)⁻¹ - regularizedCauchyKernel δ (z - w)) • h w) := by
    convert! h0.sub h1 using 1
    funext w
    exact sub_smul _ _ _
  have hint : ‖∫ w : ℂ,
      ((z - w)⁻¹ - regularizedCauchyKernel δ (z - w)) • h w‖ ≤ (4 * Real.pi * δ) * B := by
    calc
      _ ≤ ∫ w : ℂ, ‖((z - w)⁻¹ - regularizedCauchyKernel δ (z - w)) • h w‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ w : ℂ, ‖(z - w)⁻¹ - regularizedCauchyKernel δ (z - w)‖ * B := by
        apply integral_mono_ae hi.norm (hk.1.norm.mul_const B)
        filter_upwards with w
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hb w) (norm_nonneg _)
      _ = (∫ w : ℂ, ‖(z - w)⁻¹ - regularizedCauchyKernel δ (z - w)‖) * B :=
        integral_mul_const B _
      _ ≤ _ := mul_le_mul_of_nonneg_right hk.2 hB
  have heq : cauchyOperator h z - regularizedCauchyOperator δ h z =
      (Real.pi : ℂ)⁻¹ • ∫ w : ℂ,
        ((z - w)⁻¹ - regularizedCauchyKernel δ (z - w)) • h w := by
    rw [cauchyOperator, regularizedCauchyOperator, ← smul_sub, ← integral_sub h0 h1]
    simp only [sub_smul]
  rw [heq, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * ((4 * Real.pi * δ) * B) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by field_simp




theorem continuous_cauchyOperator_of_bound [CompleteSpace E] {h : ℂ → E} {R B : ℝ}
    (hB : 0 ≤ B) (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ w, ‖h w‖ ≤ B) : Continuous (cauchyOperator h) := by
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => 4 * δ n * B) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_const_nhds (x := (4 : ℝ))).mul hδlim).mul_const B
  have hu : TendstoUniformly (fun n => regularizedCauchyOperator (δ n) h)
      (cauchyOperator h) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with n hn z
    rw [dist_eq_norm]
    exact (norm_sub_regularizedCauchyOperator_le (hδ n) hB hh hs hb z).trans_lt hn
  apply hu.continuous
  exact (Eventually.of_forall fun n =>
    continuous_regularizedCauchyOperator (hδ n) hh hs hb).frequently

end PoincareConjecture.M65Branch
