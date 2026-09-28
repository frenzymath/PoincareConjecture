import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchRegularizedKernel
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyMeasurable











noncomputable section

set_option autoImplicit false

open Set MeasureTheory Metric Filter
open scoped Topology

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E]



theorem integrable_of_bound_support {h : ℂ → E} {R B : ℝ}
    (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ w, ‖h w‖ ≤ B) : Integrable h := by
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  have hc : IntegrableOn (fun _ : ℂ => B) (closedBall (0 : ℂ) R) :=
    integrableOn_const (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
  apply hc.mono' hh.restrict
  exact ae_of_all _ hb

variable [NormedSpace ℂ E]



def regularizedCauchyOperator (δ : ℝ) (h : ℂ → E) (z : ℂ) : E :=
  (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, regularizedCauchyKernel δ (z - w) • h w




theorem integrable_regularizedCauchyOperator {h : ℂ → E} {δ R B : ℝ}
    (hδ : 0 < δ) (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ w, ‖h w‖ ≤ B) (z : ℂ) :
    Integrable (fun w : ℂ => regularizedCauchyKernel δ (z - w) • h w) := by
  have hm : AEStronglyMeasurable
      (fun w : ℂ => regularizedCauchyKernel δ (z - w) • h w) volume :=
    ((continuous_regularizedCauchyKernel hδ).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.smul hh
  apply ((integrable_of_bound_support hh hs hb).norm.const_mul δ⁻¹).mono' hm
  filter_upwards with w
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_regularizedCauchyKernel_le hδ (z - w))
    (norm_nonneg _)




theorem continuous_regularizedCauchyOperator [CompleteSpace E]
    {h : ℂ → E} {δ R B : ℝ} (hδ : 0 < δ)
    (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ w, ‖h w‖ ≤ B) : Continuous (regularizedCauchyOperator δ h) := by
  have hkernel := continuous_regularizedCauchyKernel hδ
  have hdom := ((integrable_of_bound_support hh hs hb).norm.const_mul δ⁻¹)
  have hi : Continuous (fun z : ℂ => ∫ w : ℂ, regularizedCauchyKernel δ (z - w) • h w) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply continuousAt_of_dominated (bound := fun w => δ⁻¹ * ‖h w‖)
    · exact Eventually.of_forall fun t =>
        (hkernel.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul hh
    · filter_upwards with t
      filter_upwards with w
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_regularizedCauchyKernel_le hδ (t - w))
        (norm_nonneg _)
    · exact hdom
    · exact ae_of_all _ fun w =>
        (show Continuous (fun t : ℂ => regularizedCauchyKernel δ (t - w) • h w) from
          (hkernel.comp (continuous_id.sub continuous_const)).smul continuous_const).continuousAt
  exact hi.const_smul (Real.pi : ℂ)⁻¹

end PoincareConjecture.M65Branch
