import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.Cauchy.WeakInverse
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Genuine convolution calculus for the weak CR equation

The actual compact kernel derivative commutes with convolution against
a locally integrable function. The translated kernel is an actual
smooth test, so the weak equation gives zero dbar where its support
stays in the domain. Source: M65 derivation 32, continuous weak-CR
regularization, for MT Lemma 19.2, printed pp. 438--439;
Eschenburg--Tribuzy, Cauchy--Riemann inequalities, preprint pp. 8--11.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Complex
open scoped Topology ContDiff SchwartzMap Convolution

namespace PoincareMT.M65Branch

/-- The true dbar derivative of a smooth-kernel convolution is the
literal derivative-kernel integral. Source: derivation 32, continuous
weak-CR regularization, for MT 19.2, pp. 438--439. -/
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

/-- The actual weak CR identity makes every admissible translated
smooth-kernel convolution holomorphic at the evaluation point.
Source: derivation 32, continuous weak-CR regularization, for
MT 19.2, pp. 438--439. -/
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

end PoincareMT.M65Branch
