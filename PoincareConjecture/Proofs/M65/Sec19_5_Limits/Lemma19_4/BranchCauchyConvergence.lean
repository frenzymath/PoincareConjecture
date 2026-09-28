import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyContinuity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]




theorem norm_regularizedCauchyOperator_le_l1 {h : ℂ → E} {δ : ℝ}
    (hδ : 0 < δ) (hh : Integrable h) (z : ℂ) :
    ‖regularizedCauchyOperator δ h z‖ ≤
      Real.pi⁻¹ * δ⁻¹ * ∫ w : ℂ, ‖h w‖ := by
  have hm : AEStronglyMeasurable
      (fun w => regularizedCauchyKernel δ (z - w) • h w) volume :=
    (((continuous_regularizedCauchyKernel hδ).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable).smul hh.1
  have hb (w : ℂ) : ‖regularizedCauchyKernel δ (z - w) • h w‖ ≤ δ⁻¹ * ‖h w‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_regularizedCauchyKernel_le hδ _)
      (norm_nonneg _)
  have hi := (hh.norm.const_mul δ⁻¹).mono' hm (ae_of_all _ hb)
  have hle : ‖∫ w : ℂ, regularizedCauchyKernel δ (z - w) • h w‖ ≤
      δ⁻¹ * ∫ w : ℂ, ‖h w‖ := by
    calc
      _ ≤ ∫ w : ℂ, ‖regularizedCauchyKernel δ (z - w) • h w‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ w : ℂ, δ⁻¹ * ‖h w‖ :=
        integral_mono_ae hi.norm (hh.norm.const_mul _) (ae_of_all _ hb)
      _ = _ := integral_const_mul _ _
  rw [regularizedCauchyOperator, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_assoc]
  exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr Real.pi_pos.le)





theorem tendstoUniformly_cauchyOperator_of_l1
    {f : ℕ → ℂ → E} {g : ℂ → E} {R B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    (hg : AEStronglyMeasurable g volume)
    (hfs : ∀ n, Function.support (f n) ⊆ closedBall (0 : ℂ) R)
    (hgs : Function.support g ⊆ closedBall (0 : ℂ) R)
    (hfb : ∀ n z, ‖f n z‖ ≤ B) (hgb : ∀ z, ‖g z‖ ≤ B)
    (hl1 : Tendsto (fun n => ∫ z : ℂ, ‖f n z - g z‖) atTop (𝓝 0)) :
    TendstoUniformly (fun n => cauchyOperator (f n)) (cauchyOperator g) atTop := by
  have hs (n : ℕ) : Function.support (f n - g) ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    by_contra hzR
    have hf0 : f n z = 0 := Function.notMem_support.mp (fun h => hzR (hfs n h))
    have hg0 : g z = 0 := Function.notMem_support.mp (fun h => hzR (hgs h))
    exact hz (by simp only [Pi.sub_apply, hf0, hg0, sub_self])
  have hb (n : ℕ) (z : ℂ) : ‖(f n - g) z‖ ≤ 2 * B := by
    exact (norm_sub_le _ _).trans ((add_le_add (hfb n z) (hgb z)).trans_eq (by ring))
  have hi (n : ℕ) : Integrable (f n - g) :=
    (integrable_of_bound_support (hf n) (hfs n) (hfb n)).sub
      (integrable_of_bound_support hg hgs hgb)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (half_pos hε) (8 * B)
  have hlim : Tendsto (fun n => Real.pi⁻¹ * δ⁻¹ * ∫ z : ℂ, ‖f n z - g z‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hl1.const_mul (Real.pi⁻¹ * δ⁻¹)
  filter_upwards [hlim.eventually (Iio_mem_nhds (half_pos hε))] with n hn z
  have hnorm : ‖cauchyOperator (f n - g) z‖ ≤
      8 * δ * B + Real.pi⁻¹ * δ⁻¹ * ∫ w : ℂ, ‖f n w - g w‖ := by
    calc
      _ ≤ ‖cauchyOperator (f n - g) z - regularizedCauchyOperator δ (f n - g) z‖ +
          ‖regularizedCauchyOperator δ (f n - g) z‖ := norm_le_norm_sub_add _ _
      _ ≤ 4 * δ * (2 * B) + Real.pi⁻¹ * δ⁻¹ * ∫ w : ℂ, ‖(f n - g) w‖ :=
        add_le_add (norm_sub_regularizedCauchyOperator_le hδ (by positivity)
          ((hf n).sub hg) (hs n) (hb n) z)
          (norm_regularizedCauchyOperator_le_l1 hδ (hi n) z)
      _ = _ := by simp only [Pi.sub_apply]; ring
  rw [cauchyOperator_sub_of_bound (hf n) hg (hfs n) hgs (hfb n) hgb z] at hnorm
  rw [dist_comm, dist_eq_norm]
  exact hnorm.trans_lt (by nlinarith only [hsmall, hn])

end PoincareConjecture.M65Branch
