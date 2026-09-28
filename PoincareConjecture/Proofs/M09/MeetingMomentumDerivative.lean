import PoincareConjecture.Proofs.M09.LocalMinimumHessian
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Prod








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem localMin_meetingMomentum_deriv_eq_zero
    (C : ℝ × E → ℝ) (a : ℝ → E) (R : ℝ → E →L[ℝ] ℝ)
    (hC : ContDiffAt ℝ ∞ C (0, 0)) (hmin : IsLocalMin C (0, 0))
    (ha : ContDiffAt ℝ ∞ a 0) (ha0 : deriv a 0 = 0)
    (hR : DifferentiableAt ℝ R 0)
    (hfirst : ∀ᶠ t in 𝓝 (0 : ℝ), fderiv ℝ C (t, 0) (1, 0) = R t (deriv a t))
    (hsecond : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v, fderiv ℝ C (t, 0) (0, v) = R t v) :
    deriv R 0 = 0 := by
  have hR0 : R 0 = 0 := by
    ext v
    have h := hsecond.self_of_nhds v
    rw [hmin.fderiv_eq_zero] at h
    exact h.symm
  have hDC : DifferentiableAt ℝ (fderiv ℝ C) (0, (0 : E)) :=
    (hC.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hpartial (v : ℝ × E) :
      HasDerivAt (fun t ↦ fderiv ℝ C (t, 0) v)
        (fderiv ℝ (fderiv ℝ C) (0, 0) (1, 0) v) 0 := by
    simpa using (hDC.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : E)))).clm_apply
        (hasDerivAt_const (0 : ℝ) v)
  have hDa : DifferentiableAt ℝ (deriv a) 0 :=
    (ha.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hproduct : HasDerivAt (fun t ↦ R t (deriv a t)) 0 0 := by
    simpa only [ha0, hR0, map_zero, ContinuousLinearMap.zero_apply, add_zero] using
      hR.hasDerivAt.clm_apply hDa.hasDerivAt
  have hdiag : fderiv ℝ (fderiv ℝ C) (0, 0) (1, 0) (1, 0) = 0 :=
    (hpartial (1, 0)).unique (hproduct.congr_of_eventuallyEq hfirst)
  ext v
  have hkernel := localMin_secondFDeriv_zero_diagonal C (0, 0) hC hmin (1, 0) hdiag (0, v)
  have hvertical : HasDerivAt (fun t ↦ R t v) (deriv R 0 v) 0 := by
    simpa only [map_zero, add_zero] using hR.hasDerivAt.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have heq : (fun t ↦ fderiv ℝ C (t, 0) (0, v)) =ᶠ[𝓝 (0 : ℝ)] fun t ↦ R t v :=
    hsecond.mono (fun _ h ↦ h v)
  exact ((hpartial (0, v)).unique (hvertical.congr_of_eventuallyEq heq)).symm.trans hkernel

end PoincareConjecture.Proofs.M09
