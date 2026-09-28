import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.L2Product
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

set_option autoImplicit false

noncomputable section

namespace Poincare.Analysis.Dirichlet

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

private def kernelFunctional (K : Lp ℝ 2 (μ.prod ν)) (f : Lp ℝ 2 ν) :
    Lp ℝ 2 μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun h => ⟪K, tensorL2 h f⟫_ℝ
      map_add' := by
        intro h u
        simp only [tensorL2_add_left, inner_add_right]
      map_smul' := by
        intro c h
        simp only [tensorL2_smul_left, inner_smul_right, RingHom.id_apply, smul_eq_mul] }
    (‖K‖ * ‖f‖) (fun h => by
      calc
        ‖⟪K, tensorL2 h f⟫_ℝ‖ ≤ ‖K‖ * (‖h‖ * ‖f‖) := by
          simpa only [norm_tensorL2] using norm_inner_le_norm K (tensorL2 h f)
        _ = (‖K‖ * ‖f‖) * ‖h‖ := by ring)

private theorem norm_kernelFunctional_le (K : Lp ℝ 2 (μ.prod ν)) (f : Lp ℝ 2 ν) :
    ‖kernelFunctional K f‖ ≤ ‖K‖ * ‖f‖ := by
  apply (kernelFunctional K f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro h
  change ‖⟪K, tensorL2 h f⟫_ℝ‖ ≤ _
  calc
    ‖⟪K, tensorL2 h f⟫_ℝ‖ ≤ ‖K‖ * ‖tensorL2 h f‖ := norm_inner_le_norm _ _
    _ = (‖K‖ * ‖f‖) * ‖h‖ := by rw [norm_tensorL2]; ring

private def kernelDualOperator (K : Lp ℝ 2 (μ.prod ν)) :
    Lp ℝ 2 ν →L[ℝ] (Lp ℝ 2 μ →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := kernelFunctional K
      map_add' := by
        intro f g
        ext h
        change ⟪K, tensorL2 h (f + g)⟫_ℝ =
          ⟪K, tensorL2 h f⟫_ℝ + ⟪K, tensorL2 h g⟫_ℝ
        rw [tensorL2_add_right, inner_add_right]
      map_smul' := by
        intro c f
        ext h
        change ⟪K, tensorL2 h (c • f)⟫_ℝ = c * ⟪K, tensorL2 h f⟫_ℝ
        rw [tensorL2_smul_right, inner_smul_right] }
    ‖K‖ (norm_kernelFunctional_le K)

def kernelOperator (K : Lp ℝ 2 (μ.prod ν)) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (kernelDualOperator K)

theorem inner_kernelOperator (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 ν) (h : Lp ℝ 2 μ) :
    ⟪kernelOperator K f, h⟫_ℝ = ⟪K, tensorL2 h f⟫_ℝ := by
  change ⟪(InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (kernelFunctional K f), h⟫_ℝ = _
  exact InnerProductSpace.toDual_symm_apply

theorem norm_kernelOperator_apply_le (K : Lp ℝ 2 (μ.prod ν)) (f : Lp ℝ 2 ν) :
    ‖kernelOperator K f‖ ≤ ‖K‖ * ‖f‖ := by
  change ‖(InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (kernelFunctional K f)‖ ≤ _
  rw [(InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm.norm_map]
  exact norm_kernelFunctional_le K f

theorem norm_kernelOperator_le (K : Lp ℝ 2 (μ.prod ν)) : ‖kernelOperator K‖ ≤ ‖K‖ :=
  (kernelOperator K).opNorm_le_bound (norm_nonneg _) (norm_kernelOperator_apply_le K)

section IntegralAction

variable [IsFiniteMeasure μ]

omit [SFinite μ] in
theorem integrable_kernel_mul (K : Lp ℝ 2 (μ.prod ν)) (f : Lp ℝ 2 ν) :
    Integrable (fun z : α × β => K z * f z.2) (μ.prod ν) :=
  (Lp.memLp K).integrable_mul ((Lp.memLp f).comp_snd μ)

theorem kernel_sections_integrable_ae (K : Lp ℝ 2 (μ.prod ν)) (f : Lp ℝ 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * f y) ν :=
  (integrable_kernel_mul K f).prod_right_ae

private theorem setIntegral_kernelOperator (K : Lp ℝ 2 (μ.prod ν)) (f : Lp ℝ 2 ν)
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s < ∞) :
    ∫ x in s, kernelOperator K f x ∂μ = ∫ x in s, ∫ y, K (x, y) * f y ∂ν ∂μ := by
  let h : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℝ)
  let W : α × β → ℝ := fun z => K z * f z.2
  have hW : Integrable W (μ.prod ν) := integrable_kernel_mul K f
  calc
    ∫ x in s, kernelOperator K f x ∂μ = ⟪kernelOperator K f, h⟫_ℝ := by
      rw [real_inner_comm]
      exact (L2.inner_indicatorConstLp_one hs hμs.ne (kernelOperator K f)).symm
    _ = ⟪K, tensorL2 h f⟫_ℝ := inner_kernelOperator K f h
    _ = ∫ z, (Prod.fst ⁻¹' s).indicator W z ∂μ.prod ν := by
      rw [L2.inner_def]
      apply integral_congr_ae
      have hh : (h : α → ℝ) =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) :=
        indicatorConstLp_coeFn
      filter_upwards [tensorL2_ae h f,
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp hh]
        with z ht hz
      simp only [Function.comp_def] at hz
      rw [ht, hz]
      by_cases hzs : z.1 ∈ s <;>
        simp [Set.indicator, hzs, W, RCLike.inner_apply, mul_comm]
    _ = ∫ x in s, ∫ y, K (x, y) * f y ∂ν ∂μ := by
      rw [integral_prod _ (hW.indicator (measurable_fst hs))]
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs, W]

theorem kernelOperator_ae (K : Lp ℝ 2 (μ.prod ν)) (f : Lp ℝ 2 ν) :
    (kernelOperator K f : α → ℝ) =ᵐ[μ] fun x => ∫ y, K (x, y) * f y ∂ν := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq
    (kernelOperator K f) (fun x => ∫ y, K (x, y) * f y ∂ν)
    ((Lp.memLp (kernelOperator K f)).integrable (by norm_num))
    (integrable_kernel_mul K f).integral_prod_left
  exact setIntegral_kernelOperator K f

theorem memLp_kernel_integral (K : Lp ℝ 2 (μ.prod ν)) (f : Lp ℝ 2 ν) :
    MemLp (fun x => ∫ y, K (x, y) * f y ∂ν) 2 μ :=
  (memLp_congr_ae (kernelOperator_ae K f)).mp (Lp.memLp (kernelOperator K f))

end IntegralAction

end Poincare.Analysis.Dirichlet
