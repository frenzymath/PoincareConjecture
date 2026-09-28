import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchWeakCRConvolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Complex.LocallyUniformLimit













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory Complex
open scoped Topology ContDiff SchwartzMap Convolution

namespace PoincareConjecture.M65Branch





theorem tendstoLocallyUniformlyOn_bump_convolution {F : ℂ → ℂ} {U : Set ℂ}
    (hF : LocallyIntegrable F volume) (hU : IsOpen U) (hc : ContinuousOn F U)
    (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F)
      F atTop U := by
  apply hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro x hx
  have hcx : ContinuousAt F x := (hc x hx).continuousAt (hU.mem_nhds hx)
  have hval : Tendsto (fun p : ℕ × ℂ => F p.2) (atTop ×ˢ 𝓝 x) (𝓝 (F x)) :=
    hcx.tendsto.comp tendsto_snd
  have hconv : Tendsto (fun p : ℕ × ℂ =>
      ((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (F x)) :=
    ContDiffBump.convolution_tendsto_right (φ := fun p : ℕ × ℂ => φ p.1)
      (g := fun _ => F) (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hF.aestronglyMeasurable)
      (hcx.tendsto.comp tendsto_snd) tendsto_snd
  exact (hval.prodMk_nhds hconv).mono_right (nhds_le_uniformity (F x))





theorem differentiableOn_of_weak_dbar_eq_zero {F : ℂ → ℂ} {U : Set ℂ}
    (hF : LocallyIntegrable F volume) (hU : IsOpen U) (hc : ContinuousOn F U)
    (hweak : ∀ ψ : 𝓢(ℂ, ℂ), HasCompactSupport (ψ : ℂ → ℂ) →
      tsupport (ψ : ℂ → ℂ) ⊆ U → (∫ w, dbar ψ w * F w) = 0) :
    DifferentiableOn ℂ F U := by
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φ (n : ℕ) : ContDiffBump (0 : ℂ) :=
    { rIn := δ n / 3
      rOut := δ n
      rIn_pos := div_pos (hδ n) (by norm_num)
      rIn_lt_rOut := by linarith [hδ n] }
  let f (n : ℕ) : ℂ → ℂ :=
    (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
  let k (n : ℕ) (z : ℂ) : ℂ := (φ n).normed volume z
  have hks (n : ℕ) : tsupport (k n) ⊆ closedBall (0 : ℂ) (δ n) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro z hz
    have hz' : z ∈ Function.support ((φ n).normed volume) := by
      intro hz0
      apply hz
      change ((φ n).normed volume z : ℂ) = 0
      rw [hz0]
      simp
    rw [(φ n).support_normed_eq] at hz'
    exact ball_subset_closedBall hz'
  have hkc (n : ℕ) : HasCompactSupport (k n) :=
    (isCompact_closedBall (0 : ℂ) (δ n)).of_isClosed_subset (isClosed_tsupport _) (hks n)
  have hk (n : ℕ) : ContDiff ℝ ∞ (k n) :=
    ofRealCLM.contDiff.comp (φ n).contDiff_normed
  have hsame (n : ℕ) :
      (k n ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] F) = f n := by
    funext z
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, k,
      real_smul]
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ n).contDiff_normed hF
  have hconv : TendstoLocallyUniformlyOn f F atTop U :=
    tendstoLocallyUniformlyOn_bump_convolution hF hU hc φ hδ0
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hhalf : 0 < r / 2 := half_pos hr
  have hsmall : ∀ᶠ n in atTop, δ n < r / 2 := hδ0.eventually (gt_mem_nhds hhalf)
  have hhol : ∀ᶠ n in atTop, DifferentiableOn ℂ (f n) (ball x (r / 2)) := by
    filter_upwards [hsmall] with n hn y hy
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_complex_of_dbar_eq_zero ((hf n).differentiable (by simp) y)
    rw [← hsame n]
    apply dbar_convolution_eq_zero_of_weak (hk n) (hkc n) hF hweak y
    intro w hw
    apply hsub
    have hwy : dist w y ≤ δ n := by
      have he := mem_closedBall_zero_iff.mp (hks n hw)
      simpa only [dist_eq_norm, norm_sub_rev] using he
    exact mem_ball.mpr ((dist_triangle w y x).trans_lt (by
      have hy' := mem_ball.mp hy
      linarith))
  have hFU : ball x (r / 2) ⊆ U :=
    (ball_subset_ball (by linarith)).trans hsub
  exact (((hconv.mono hFU).differentiableOn hhol isOpen_ball).differentiableAt
    (ball_mem_nhds x hhalf)).differentiableWithinAt

end PoincareConjecture.M65Branch
