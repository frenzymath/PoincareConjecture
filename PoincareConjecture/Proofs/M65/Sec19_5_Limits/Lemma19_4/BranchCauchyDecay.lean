import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyContinuity
import Mathlib.Analysis.Normed.Field.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem tendsto_cauchyOperator_cocompact {h : ℂ → E} {R B : ℝ}
    (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ w, ‖h w‖ ≤ B) :
    Tendsto (cauchyOperator h) (cocompact ℂ) (𝓝 0) := by
  let : (cocompact ℂ).IsCountablyGenerated := by
    rw [← (cobounded_eq_cocompact (α := ℂ)), ← (comap_norm_atTop (E := ℂ))]
    infer_instance
  have hi := integrable_of_bound_support hh hs hb
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  have hp (w : ℂ) : Tendsto (fun z : ℂ => (z - w)⁻¹ • h w)
      (cocompact ℂ) (𝓝 0) := by
    have ht : Tendsto (fun z : ℂ => z - w) (cocompact ℂ) (cocompact ℂ) := by
      simpa only [sub_eq_add_neg, Homeomorph.coe_addRight] using
        (show Tendsto (Homeomorph.addRight (-w)) (cocompact ℂ) (cocompact ℂ) from
          le_of_eq (Homeomorph.addRight (-w)).map_cocompact)
    have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa only [cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded (α := ℂ))
    simpa only [zero_smul, Function.comp_apply] using (hinv.comp ht).smul_const (h w)
  have hbound : ∀ᶠ z in cocompact ℂ, ∀ᵐ w ∂volume,
      ‖(z - w)⁻¹ • h w‖ ≤ ‖h w‖ := by
    filter_upwards [hnorm.eventually (eventually_ge_atTop (R + 1))] with z hz
    filter_upwards with w
    by_cases hw : w ∈ closedBall (0 : ℂ) R
    · have hwR : ‖w‖ ≤ R := mem_closedBall_zero_iff.mp hw
      have hzw : 1 ≤ ‖z - w‖ := by linarith [norm_sub_norm_le z w]
      rw [norm_smul, norm_inv]
      have hk : ‖z - w‖⁻¹ ≤ 1 := by
        simpa only [one_div, inv_one] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hzw
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (norm_nonneg (h w))
    · have hzero : h w = 0 := Function.notMem_support.mp (fun hw' => hw (hs hw'))
      simp only [hzero, smul_zero, norm_zero, le_refl]
  have hint : Tendsto (fun z => ∫ w : ℂ, (z - w)⁻¹ • h w)
      (cocompact ℂ) (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun w => ‖h w‖)
      (Eventually.of_forall fun z =>
        (integrable_cauchyOperator_of_bound hh hs hb z).aestronglyMeasurable)
      hbound hi.norm (ae_of_all _ hp)
  change Tendsto (fun z => (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, (z - w)⁻¹ • h w)
    (cocompact ℂ) (𝓝 0)
  simpa only [smul_zero] using hint.const_smul (Real.pi : ℂ)⁻¹

end PoincareConjecture.M65Branch
