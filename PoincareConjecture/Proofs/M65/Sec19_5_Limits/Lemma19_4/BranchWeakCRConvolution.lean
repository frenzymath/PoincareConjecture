import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyWeakInverse
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Complex
open scoped Topology ContDiff SchwartzMap Convolution

namespace PoincareConjecture.M65Branch

theorem dbar_convolution_smooth_left {k F : ℂ → ℂ}
    (hk : ContDiff ℝ 1 k) (hs : HasCompactSupport k)
    (hF : LocallyIntegrable F volume) (x : ℂ) :
    dbar (k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] F) x =
      ∫ w, dbar k (x - w) * F w := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  have hd (v : ℂ) :
      fderiv ℝ (k ⋆[L, volume] F) x v = ∫ w, fderiv ℝ k (x - w) v * F w := by
    rw [← convolution_flip]
    have h := hs.hasFDerivAt_convolution_right L.flip hF hk x
    rw [h.fderiv, convolution_precompR_apply L.flip hF (hs.fderiv ℝ)
      (hk.continuous_fderiv one_ne_zero)]
    rfl
  have hi (v : ℂ) : Integrable (fun w => fderiv ℝ k (x - w) v * F w) :=
    (hs.fderiv_apply ℝ v).convolutionExists_right L.flip hF
      ((hk.continuous_fderiv one_ne_zero).clm_apply continuous_const) x
  change dbar (k ⋆[L, volume] F) x = _
  simp only [dbar, dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply,
    smul_eq_mul, hd]
  rw [← integral_const_mul, ← integral_add (hi 1) ((hi I).const_mul I),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  ring

theorem dbar_convolution_eq_zero_of_weak {k F : ℂ → ℂ} {U : Set ℂ}
    (hk : ContDiff ℝ ∞ k) (hs : HasCompactSupport k)
    (hF : LocallyIntegrable F volume)
    (hweak : ∀ φ : 𝓢(ℂ, ℂ), HasCompactSupport (φ : ℂ → ℂ) →
      tsupport (φ : ℂ → ℂ) ⊆ U → (∫ w, dbar φ w * F w) = 0)
    (x : ℂ) (hU : ∀ w, x - w ∈ tsupport k → w ∈ U) :
    dbar (k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] F) x = 0 := by
  let ψ (w : ℂ) := k (x - w)
  have hψ : ContDiff ℝ ∞ ψ := hk.comp (contDiff_const.sub contDiff_id)
  have hψs : HasCompactSupport ψ := hs.comp_homeomorph (Homeomorph.subLeft x)
  have hψU : tsupport ψ ⊆ U := by
    change tsupport (k ∘ Homeomorph.subLeft x) ⊆ U
    rw [tsupport_comp_eq_preimage]
    exact fun w hw => hU w hw
  have hbar (w : ℂ) : dbar ψ w = -dbar k (x - w) := by
    have hd := ((hk.differentiable (by simp)) (x - w)).hasFDerivAt.comp w
      ((hasFDerivAt_const x w).sub (hasFDerivAt_id w))
    change HasFDerivAt ψ _ w at hd
    simp only [dbar, hd.fderiv, dbarLinear, smul_apply, add_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply,
      zero_sub, neg_apply, ContinuousLinearMap.id_apply, map_neg, smul_eq_mul]
    ring
  have htest := hweak (hψs.toSchwartzMap hψ) hψs hψU
  change (∫ w, dbar ψ w * F w) = 0 at htest
  simp_rw [hbar, neg_mul] at htest
  rw [integral_neg, neg_eq_zero] at htest
  rw [dbar_convolution_smooth_left (hk.of_le (by simp)) hs hF]
  exact htest

end PoincareConjecture.M65Branch
