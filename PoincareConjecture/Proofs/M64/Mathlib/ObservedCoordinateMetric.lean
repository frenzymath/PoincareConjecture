import PoincareConjecture.Proofs.M64.Mathlib.C2LaplacianChange

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def m64ObservedCoordinateMetric (J : E → F) (Q : E → F →L[ℝ] F →L[ℝ] ℝ)
    (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (Q y).bilinearComp (fderiv ℝ J y) (fderiv ℝ J y)

theorem m64ObservedCoordinateMetric_continuousOn
    {J : E → F} {Q : E → F →L[ℝ] F →L[ℝ] ℝ} {U K : Set E}
    (hU : IsOpen U) (hJ : ContDiffOn ℝ 1 J U) (hKU : K ⊆ U)
    (hQ : ContinuousOn Q K) : ContinuousOn (m64ObservedCoordinateMetric J Q) K := by
  have hD : ContinuousOn (fderiv ℝ J) K :=
    (hJ.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU
  have hleft := hQ.clm_comp hD
  have hflip := (ContinuousLinearMap.flipₗᵢ ℝ E F ℝ).continuous.comp_continuousOn hleft
  exact (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous.comp_continuousOn
    (hflip.clm_comp hD)

theorem m64ObservedCoordinateMetric_bounds
    {J : E → F} {H : F → E} {Q : E → F →L[ℝ] F →L[ℝ] ℝ} {U K : Set E}
    (hU : IsOpen U) (hJ : ContDiffOn ℝ 1 J U) (hH : ContDiff ℝ 1 H)
    (hKU : K ⊆ U) (hinv : EqOn (H ∘ J) id U)
    {C D L B : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hDH : ∀ y ∈ K, ‖fderiv ℝ H (J y)‖ ≤ D)
    (hDJ : ∀ y ∈ K, ‖fderiv ℝ J y‖ ≤ L)
    (hQB : ∀ y ∈ K, ‖Q y‖ ≤ B)
    (hsymm : ∀ y ∈ K, ∀ v w, Q y v w = Q y w v)
    (hpos : ∀ y ∈ K, ∀ v, 0 ≤ Q y v v)
    (hcoercive : ∀ y ∈ K, ∀ v,
      ‖fderiv ℝ J y v‖ ^ 2 ≤ C * Q y (fderiv ℝ J y v) (fderiv ℝ J y v)) :
    0 < 1 / (D ^ 2 * (C + 1)) ∧ 0 ≤ B * L ^ 2 ∧
      ∀ y ∈ K,
        (∀ v w, m64ObservedCoordinateMetric J Q y v w =
          m64ObservedCoordinateMetric J Q y w v) ∧
        (∀ v, (1 / (D ^ 2 * (C + 1))) * ‖v‖ ^ 2 ≤
          m64ObservedCoordinateMetric J Q y v v) ∧
        ∀ v, m64ObservedCoordinateMetric J Q y v v ≤ B * L ^ 2 * ‖v‖ ^ 2 := by
  have hden : 0 < D ^ 2 * (C + 1) := by positivity
  refine ⟨one_div_pos.mpr hden, mul_nonneg hB (sq_nonneg L), fun y hy => ⟨?_, ?_, ?_⟩⟩
  · intro v w
    exact hsymm y hy _ _
  · intro v
    have heq : (H ∘ J) =ᶠ[𝓝 y] id := hinv.eventuallyEq_of_mem (hU.mem_nhds (hKU hy))
    have hJy : DifferentiableAt ℝ J y :=
      (hJ.contDiffAt (hU.mem_nhds (hKU hy))).differentiableAt one_ne_zero
    have hd := congrArg (fun A : E →L[ℝ] E => A v)
      (fderiv_comp y (hH.differentiable one_ne_zero _) hJy)
    rw [heq.fderiv_eq, fderiv_id] at hd
    have hnorm : ‖v‖ ≤ D * ‖fderiv ℝ J y v‖ := by
      calc
        _ = ‖fderiv ℝ H (J y) (fderiv ℝ J y v)‖ := congrArg norm hd
        _ ≤ _ := ((fderiv ℝ H (J y)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hDH y hy) (norm_nonneg _))
    have hs : ‖v‖ ^ 2 ≤ D ^ 2 * ‖fderiv ℝ J y v‖ ^ 2 := by
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD.le (norm_nonneg _))).mpr hnorm
    have hbound : ‖v‖ ^ 2 ≤ D ^ 2 * (C + 1) *
        Q y (fderiv ℝ J y v) (fderiv ℝ J y v) := by
      calc
        _ ≤ D ^ 2 * (C * Q y (fderiv ℝ J y v) (fderiv ℝ J y v)) :=
          hs.trans (mul_le_mul_of_nonneg_left (hcoercive y hy v) (sq_nonneg D))
        _ ≤ _ := by nlinarith [hpos y hy (fderiv ℝ J y v), sq_nonneg D]
    change (1 / (D ^ 2 * (C + 1))) * ‖v‖ ^ 2 ≤
      Q y (fderiv ℝ J y v) (fderiv ℝ J y v)
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hbound)
  · intro v
    have hnorm : ‖fderiv ℝ J y v‖ ≤ L * ‖v‖ :=
      ((fderiv ℝ J y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hDJ y hy) (norm_nonneg v))
    have hs : ‖fderiv ℝ J y v‖ ^ 2 ≤ L ^ 2 * ‖v‖ ^ 2 := by
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr hnorm
    change Q y (fderiv ℝ J y v) (fderiv ℝ J y v) ≤ _
    calc
      _ ≤ |Q y (fderiv ℝ J y v) (fderiv ℝ J y v)| := le_abs_self _
      _ ≤ ‖Q y‖ * ‖fderiv ℝ J y v‖ * ‖fderiv ℝ J y v‖ :=
        (Q y).le_opNorm₂ _ _
      _ ≤ B * ‖fderiv ℝ J y v‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right (hQB y hy) (sq_nonneg ‖fderiv ℝ J y v‖)]
      _ ≤ B * (L ^ 2 * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hs hB
      _ = _ := by ring

end PoincareConjecture
