import PoincareConjecture.Proofs.M38.BallShrinking
import Mathlib.Analysis.Calculus.ImplicitContDiff










set_option autoImplicit false

open Set Topology Filter
open scoped ContDiff

namespace PoincareConjecture.M38


noncomputable def parameterizedBallShrinkInverse (c : ℝ) : ℝ → ℝ :=
  Function.invFun (ballShrinkProfile c)


theorem parameterizedBallShrinkInverse_right {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (t : ℝ) : ballShrinkProfile c (parameterizedBallShrinkInverse c t) = t :=
  Function.rightInverse_invFun (ballShrinkProfile_surjective hc hc1) t


theorem parameterizedBallShrinkInverse_left {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (t : ℝ) : parameterizedBallShrinkInverse c (ballShrinkProfile c t) = t :=
  Function.leftInverse_invFun (ballShrinkProfile_strictMono hc hc1).injective t


theorem parameterizedBallShrinkInverse_eq {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (t : ℝ) : parameterizedBallShrinkInverse c t = (ballShrinkOrderIso c hc hc1).symm t := by
  apply (ballShrinkProfile_strictMono hc hc1).injective
  rw [parameterizedBallShrinkInverse_right hc hc1]
  exact (ballShrinkOrderIso c hc hc1).apply_symm_apply t |>.symm


theorem parameterizedBallShrinkInverse_zero {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    parameterizedBallShrinkInverse c 0 = 0 := by
  rw [parameterizedBallShrinkInverse_eq hc hc1, ballShrinkOrderIso_symm_zero hc hc1]


theorem parameterizedBallShrinkInverse_pos {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {t : ℝ} (ht : 0 < t) : 0 < parameterizedBallShrinkInverse c t := by
  rw [parameterizedBallShrinkInverse_eq hc hc1]
  simpa only [ballShrinkOrderIso_symm_zero hc hc1] using
    (ballShrinkOrderIso c hc hc1).symm.strictMono ht


theorem parameterizedBallShrinkInverse_outer {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {t : ℝ} (ht : 3 / 2 ≤ t) : parameterizedBallShrinkInverse c t = t := by
  calc
    parameterizedBallShrinkInverse c t =
        parameterizedBallShrinkInverse c (ballShrinkProfile c t) :=
      congrArg (parameterizedBallShrinkInverse c) (ballShrinkProfile_outer c t ht).symm
    _ = t := parameterizedBallShrinkInverse_left hc hc1 t


theorem parameterizedBallShrinkInverse_linear {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {t : ℝ} (ht : t ≤ c * (5 / 4)) : parameterizedBallShrinkInverse c t = t / c := by
  rw [parameterizedBallShrinkInverse_eq hc hc1]
  exact ballShrinkOrderIso_symm_linear hc hc1 t ht


theorem ballShrinkProfile_joint_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => ballShrinkProfile p.1 p.2) :=
  (contDiff_fst.mul contDiff_snd).add
    ((contDiff_const.sub contDiff_fst).mul (ballShrinkTransition_smooth.comp contDiff_snd))


noncomputable def ballShrinkImplicitResidual (p : (ℝ × ℝ) × ℝ) : ℝ :=
  ballShrinkProfile p.1.1 p.2 - p.1.2


theorem ballShrinkImplicitResidual_smooth : ContDiff ℝ ∞ ballShrinkImplicitResidual :=
  (ballShrinkProfile_joint_smooth.comp
    ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).sub
      (contDiff_snd.comp contDiff_fst)


theorem ballShrinkImplicitResidual_partial_invertible {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (t s : ℝ) :
    ((fderiv ℝ ballShrinkImplicitResidual ((c, t), s)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible := by
  have hinr : HasFDerivAt (fun u : ℝ => ((c, t), u))
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) s :=
    (hasFDerivAt_const (c, t) s).prodMk (hasFDerivAt_id s)
  have hfull := (ballShrinkImplicitResidual_smooth.differentiable (by simp) ((c, t), s)).hasFDerivAt
  have hscalar : HasDerivAt (fun u => ballShrinkProfile c u - t)
      (deriv (ballShrinkProfile c) s) s :=
    ((ballShrinkProfile_smooth c).differentiable (by simp) s).hasDerivAt.sub_const t
  have heq := (hfull.comp s hinr).unique
    (hscalar.hasFDerivAt_equiv (ballShrinkProfile_deriv_pos hc hc1 s).ne')
  rw [heq]
  exact ContinuousLinearMap.isInvertible_equiv


theorem parameterizedBallShrinkInverse_contDiffAt {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (t : ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => parameterizedBallShrinkInverse p.1 p.2) (c, t) := by
  let s := parameterizedBallShrinkInverse c t
  have hs : ballShrinkImplicitResidual ((c, t), s) = 0 := by
    change ballShrinkProfile c (parameterizedBallShrinkInverse c t) - t = 0
    rw [parameterizedBallShrinkInverse_right hc hc1, sub_self]
  have hF : ContDiffAt ℝ ∞ ballShrinkImplicitResidual ((c, t), s) :=
    ballShrinkImplicitResidual_smooth.contDiffAt
  have hi := ballShrinkImplicitResidual_partial_invertible hc hc1 t s
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ := hF.implicitFunction hn hi
  have hψ : ContDiffAt ℝ ∞ ψ (c, t) := hF.contDiffAt_implicitFunction hn hi
  have heq : ∀ᶠ p : ℝ × ℝ in 𝓝 (c, t),
      ballShrinkProfile p.1 (ψ p) = p.2 := by
    filter_upwards [hF.eventually_apply_implicitFunction hn hi] with p hp
    change ballShrinkProfile p.1 (ψ p) - p.2 = ballShrinkImplicitResidual ((c, t), s) at hp
    rw [hs] at hp
    exact sub_eq_zero.mp hp
  have hcoef : ∀ᶠ p : ℝ × ℝ in 𝓝 (c, t), 0 < p.1 ∧ p.1 < 1 :=
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hc, hc1⟩
  apply hψ.congr_of_eventuallyEq
  filter_upwards [heq, hcoef] with p hp hc'
  apply (ballShrinkProfile_strictMono hc'.1 hc'.2).injective
  rw [parameterizedBallShrinkInverse_right hc'.1 hc'.2, hp]


theorem parameterizedBallShrinkInverse_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => parameterizedBallShrinkInverse p.1 p.2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) := by
  intro p hp
  exact (parameterizedBallShrinkInverse_contDiffAt hp.1.1 hp.1.2 p.2).contDiffWithinAt

end PoincareConjecture.M38
