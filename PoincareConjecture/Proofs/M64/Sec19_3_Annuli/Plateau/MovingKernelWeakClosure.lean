import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MovingQuadraticLiminf
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

private theorem weak_norm_bounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {u : ℕ → H} {v : H} (hu : WeakConverges u v) : ∃ A : ℝ, ∀ j, ‖u j‖ ≤ A := by
  let D := InnerProductSpace.toDual ℝ H
  obtain ⟨A, hA⟩ := banach_steinhaus (g := fun j => D (u j)) (fun w => by
    have hh := hu (D w)
    obtain ⟨C, hC⟩ := hh.cauchySeq.isBounded_range.exists_norm_le
    refine ⟨C, fun j => ?_⟩
    simpa only [D, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hC _ (mem_range_self j))
  refine ⟨A, fun j => ?_⟩
  simpa only [D.norm_map] using hA j

variable {X E : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]



theorem m64MovingKernel_weak_closed
    (R : ℕ → X → E →L[ℝ] E) (R0 : X → E →L[ℝ] E)
    (hR : ∀ j, AEStronglyMeasurable (R j) mu)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ j, ∀ᵐ x ∂mu, ‖R j x‖ ≤ K)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun j => R j x) atTop (𝓝 (R0 x)))
    {u : ℕ → Lp E 2 mu} {v : Lp E 2 mu} (hu : WeakConverges u v)
    (hzero : ∀ j, ∀ᵐ x ∂mu, R j x (u j x) = 0) :
    ∀ᵐ x ∂mu, R0 x (v x) = 0 := by
  obtain ⟨A, hA⟩ := weak_norm_bounded hu
  let Q := fun T : E →L[ℝ] E => (innerSL ℝ).bilinearComp T T
  have hQ : Continuous Q := by
    apply continuous_clm_apply.mpr
    intro w
    apply continuous_clm_apply.mpr
    intro z
    exact (continuous_id.clm_apply continuous_const).inner
      (continuous_id.clm_apply continuous_const)
  have hQbound (T : E →L[ℝ] E) (hT : ‖T‖ ≤ K) : ‖Q T‖ ≤ K ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ (sq_nonneg K)
    intro w z
    change ‖inner ℝ (T w) (T z)‖ ≤ K ^ 2 * ‖w‖ * ‖z‖
    have hw : ‖T w‖ ≤ K * ‖w‖ :=
      (T.le_opNorm w).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    have hz : ‖T z‖ ≤ K * ‖z‖ :=
      (T.le_opNorm z).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    exact (norm_inner_le_norm _ _).trans
      ((mul_le_mul hw hz (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).trans_eq (by ring))
  have hR0 : AEStronglyMeasurable R0 mu := aestronglyMeasurable_of_tendsto_ae atTop hR hlim
  have hR0bound : ∀ᵐ x ∂mu, ‖R0 x‖ ≤ K := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with x hx hb
    exact le_of_tendsto hx.norm (Eventually.of_forall hb)
  have hQlim : ∀ᵐ x ∂mu, Tendsto (fun j => Q (R j x)) atTop (𝓝 (Q (R0 x))) := by
    filter_upwards [hlim] with x hx
    exact (hQ.tendsto _).comp hx
  have henergy := m64MovingQuadratic_le_liminf
    (fun j x => Q (R j x)) (fun x => Q (R0 x))
    (fun j => hQ.comp_aestronglyMeasurable (hR j)) (hQ.comp_aestronglyMeasurable hR0)
    (sq_nonneg K) (fun j => (hbound j).mono fun x hx => hQbound _ hx) hQlim
    (fun j => Eventually.of_forall fun x w => real_inner_self_nonneg)
    (fun j => Eventually.of_forall fun x w z => real_inner_comm _ _) hu hA
  have hseqzero (j : ℕ) : (∫ x, Q (R j x) (u j x) (u j x) ∂mu) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzero j] with x hx
    change inner ℝ (R j x (u j x)) (R j x (u j x)) = 0
    rw [hx, inner_zero_left]
  simp only [hseqzero, liminf_const] at henergy
  have hmeas : AEStronglyMeasurable (fun x => R0 x (v x)) mu := by
    have hc : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    exact hc.comp_aestronglyMeasurable (hR0.prodMk (Lp.aestronglyMeasurable v))
  have hresnorm : ∀ᵐ x ∂mu, ‖R0 x (v x)‖ ≤ K * ‖v x‖ := by
    filter_upwards [hR0bound] with x hx
    exact (R0 x).le_opNorm (v x) |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hlp : MemLp (fun x => R0 x (v x)) 2 mu := (Lp.memLp v).of_le_mul hmeas hresnorm
  have hint : Integrable (fun x => ‖R0 x (v x)‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm hmeas).mp hlp
  have heq : (∫ x, ‖R0 x (v x)‖ ^ 2 ∂mu) = 0 := by
    apply le_antisymm _ (integral_nonneg fun x => sq_nonneg _)
    simpa only [Q, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq] using henergy
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).mp heq
  filter_upwards [hz] with x hx
  simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] using hx

end PoincareConjecture
