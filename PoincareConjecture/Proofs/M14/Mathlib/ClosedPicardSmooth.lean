import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathSubstitution
import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathPrimitive
import PoincareConjecture.Proofs.M09.SmoothImplicit
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

noncomputable def closedPicardResidual (t₀ : Icc a b) (f : ℝ × E → E)
    (hf : ContinuousOn f (Icc a b ×ˢ univ)) (z : E × C(Icc a b, E)) : C(Icc a b, E) :=
  z.2 - ContinuousMap.const _ z.1 - closedPathPrimitive t₀ (closedTimePostcomp f hf z.2)

omit [CompleteSpace E] in

theorem closedPicardResidual_contDiff [FiniteDimensional ℝ E] (hab : a < b)
    (t₀ : Icc a b) (f : ℝ × E → E) (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ)) :
    ContDiff ℝ ∞ (closedPicardResidual t₀ f hf.continuousOn) := by
  have hconst : ContDiff ℝ ∞ (fun z : E × C(Icc a b, E) => ContinuousMap.const (Icc a b) z.1) :=
    (ContinuousLinearMap.const (R := ℝ) (M := E) (Icc a b)).contDiff.comp contDiff_fst
  exact (contDiff_snd.sub hconst).sub ((closedPathPrimitive t₀).contDiff.comp
    ((closedTimePostcomp_contDiff (uniqueDiffOn_Icc hab) f hf).comp contDiff_snd))

theorem exists_closedPicard_smooth_family [FiniteDimensional ℝ E] (hab : a < b)
    (t₀ : Icc a b) (f : ℝ × E → E) (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (x₀ : E) (φ₀ : C(Icc a b, E))
    (heq : φ₀ = ContinuousMap.const _ x₀ +
      closedPathPrimitive t₀ (closedTimePostcomp f hf.continuousOn φ₀))
    (hsmall : (b - a) * ‖closedTimePostcomp (M08.spatialWithinFDeriv (Icc a b) univ f)
      (M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) isOpen_univ f hf).continuousOn
        φ₀‖ < 1) :
    ∃ (σ : E → C(Icc a b, E)) (U : Set E) (W : Set (E × C(Icc a b, E))),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen W ∧ (x₀, φ₀) ∈ W ∧
      σ x₀ = φ₀ ∧ ContDiffOn ℝ ∞ σ U ∧
      (∀ x ∈ U, (x, σ x) ∈ W ∧ σ x = ContinuousMap.const _ x +
        closedPathPrimitive t₀ (closedTimePostcomp f hf.continuousOn (σ x))) ∧
      ∀ z ∈ W, (z.2 = ContinuousMap.const _ z.1 +
        closedPathPrimitive t₀ (closedTimePostcomp f hf.continuousOn z.2)) ↔ σ z.1 = z.2 := by
  let H := closedPicardResidual t₀ f hf.continuousOn
  let L := closedPathPrimitive (E := E) t₀
  let A := closedTimePostcomp (M08.spatialWithinFDeriv (Icc a b) univ f)
    (M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) isOpen_univ f hf).continuousOn φ₀
  let D := Proofs.M09.pointwiseLinear A
  have hS : HasFDerivAt (closedTimePostcomp f hf.continuousOn) D φ₀ :=
    hasFDerivAt_closedTimePostcomp (uniqueDiffOn_Icc hab) f hf φ₀
  have hH : ContDiff ℝ ∞ H := closedPicardResidual_contDiff hab t₀ f hf
  have hpartial : (fderiv ℝ H (x₀, φ₀)).comp (ContinuousLinearMap.inr ℝ E C(Icc a b, E)) =
      ContinuousLinearMap.id ℝ C(Icc a b, E) - L.comp D := by
    have hfull := (hH.differentiable (by simp) (x₀, φ₀)).hasFDerivAt
    have hr : HasFDerivAt (fun φ => H (x₀, φ))
        (ContinuousLinearMap.id ℝ C(Icc a b, E) - L.comp D) φ₀ :=
      ((hasFDerivAt_id φ₀).sub_const (ContinuousMap.const _ x₀)).sub (L.hasFDerivAt.comp φ₀ hS)
    exact (hfull.comp φ₀ (hasFDerivAt_prodMk_right x₀ φ₀)).unique hr
  have hnorm : ‖L.comp D‖ < 1 :=
    (L.opNorm_comp_le D).trans_lt
      ((mul_le_mul (closedPathPrimitive_norm_le t₀) (Proofs.M09.pointwiseLinear_norm_le A)
        (norm_nonneg D) (sub_nonneg.mpr hab.le)).trans_lt hsmall)
  have hinv : ((fderiv ℝ H (x₀, φ₀)).comp
      (ContinuousLinearMap.inr ℝ E C(Icc a b, E))).IsInvertible := by
    rw [hpartial]
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one (x := L.comp D) hnorm
    exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩
  have hzero : H (x₀, φ₀) = 0 := by
    change φ₀ - ContinuousMap.const _ x₀ - L (closedTimePostcomp f hf.continuousOn φ₀) = 0
    rw [sub_sub, sub_eq_zero]
    exact heq
  obtain ⟨σ, U, W, hU, hxU, hW, hxW, hi, hσ, hsol, huniq⟩ :=
    Proofs.M09.exists_smooth_implicit H hH (x₀, φ₀) hinv
  refine ⟨σ, U, W, hU, hxU, hW, hxW, hi, hσ, ?_, ?_⟩
  · intro x hx
    refine ⟨(hsol x hx).1, ?_⟩
    have h := (hsol x hx).2
    rw [hzero] at h
    simpa only [H, closedPicardResidual, sub_sub, sub_eq_zero] using h
  · intro z hz
    have h := huniq z hz
    rw [hzero] at h
    simpa only [H, closedPicardResidual, sub_sub, sub_eq_zero] using h

end PoincareConjecture.M14
