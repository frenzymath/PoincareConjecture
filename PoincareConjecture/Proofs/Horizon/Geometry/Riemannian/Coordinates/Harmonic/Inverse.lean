import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension











noncomputable section
set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal

namespace PoincareConjecture.HarmonicCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [FiniteDimensional ℝ E] [Nontrivial E] in


lemma approximates_identity_on_ball {f : E → E} {R : ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball 0 R))
    (hclose : ∀ x ∈ ball 0 R, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ApproximatesLinearOn f (ContinuousLinearMap.id ℝ E) (ball 0 R) (1 / 2) := by
  rw [ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith]
  apply (convex_ball (0 : E) R).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact ((hf.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)).sub
      (ContinuousLinearMap.id ℝ E).differentiableAt
  · intro x hx
    rw [fderiv_sub
      ((hf.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      (ContinuousLinearMap.id ℝ E).differentiableAt, ContinuousLinearMap.fderiv]
    exact hclose x hx

omit [Nontrivial E] in

lemma isInvertible_of_norm_sub_id_le_half {A : E →L[ℝ] E}
    (hA : ‖A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) : A.IsInvertible := by
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    have h := (A - ContinuousLinearMap.id ℝ E).le_opNorm v
    have hmul := mul_le_mul_of_nonneg_right hA (norm_nonneg v)
    simp only [sub_apply, ContinuousLinearMap.id_apply, hv, zero_sub,
      norm_neg] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] in

lemma norm_apply_bounds_of_norm_sub_id_le_half {A : E →L[ℝ] E}
    (hA : ‖A - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) (v : E) :
    ‖v‖ / 2 ≤ ‖A v‖ ∧ ‖A v‖ ≤ 3 * ‖v‖ / 2 := by
  have herror : ‖A v - v‖ ≤ ‖v‖ / 2 := by
    have h := (A - ContinuousLinearMap.id ℝ E).le_opNorm v
    have hmul := mul_le_mul_of_nonneg_right hA (norm_nonneg v)
    simp only [sub_apply, ContinuousLinearMap.id_apply] at h
    linarith
  constructor
  · have h := norm_sub_le (A v - v) (A v)
    have heq : A v - v - A v = -v := by abel
    rw [heq, norm_neg] at h
    linarith
  · have h := norm_add_le (A v - v) v
    rw [sub_add_cancel] at h
    linarith

omit [Nontrivial E] in


lemma norm_fderiv_symm_bounds
    (F : OpenPartialHomeomorph E E) (hF : ContDiffOn ℝ ∞ F F.source)
    (hclose : ∀ x ∈ F.source, ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2)
    {x : E} (hx : x ∈ F.target) (v : E) :
    (2 / 3 : ℝ) * ‖v‖ ≤ ‖fderiv ℝ F.symm x v‖ ∧
      ‖fderiv ℝ F.symm x v‖ ≤ 2 * ‖v‖ := by
  have hy := F.map_target hx
  have hdiff := (hF.contDiffAt (F.open_source.mem_nhds hy)).differentiableAt (by simp)
  obtain ⟨A, hA⟩ := isInvertible_of_norm_sub_id_le_half (hclose (F.symm x) hy)
  have hderiv : HasFDerivAt F (A : E →L[ℝ] E) (F.symm x) := by
    simpa only [hA] using hdiff.hasFDerivAt
  rw [(F.hasFDerivAt_symm hx hderiv).fderiv]
  simp only [ContinuousLinearEquiv.coe_coe]
  have h := norm_apply_bounds_of_norm_sub_id_le_half
    (show ‖(A : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 by
      rw [hA]; exact hclose _ hy) (A.symm v)
  simp only [ContinuousLinearEquiv.coe_coe, A.apply_symm_apply] at h
  constructor <;> linarith [h.1, h.2]



lemma exists_inverse_on_ball {f : E → E} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ ∞ f (ball 0 R)) (hf0 : f 0 = 0)
    (hclose : ∀ x ∈ ball 0 R, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ∃ F : OpenPartialHomeomorph E E,
      (F : E → E) = f ∧ F.source = ball 0 R ∧ ball 0 (R / 4) ⊆ F.target ∧
      ContDiffOn ℝ ∞ F.symm F.target ∧ F.symm 0 = 0 := by
  let L := ContinuousLinearEquiv.refl ℝ E
  have happrox : ApproximatesLinearOn f (L : E →L[ℝ] E) (ball 0 R) (1 / 2) :=
    approximates_identity_on_ball hf hclose
  have hc : Subsingleton E ∨ (1 / 2 : ℝ≥0) < ‖(L.symm : E →L[ℝ] E)‖₊⁻¹ := by
    right
    norm_num [L]
  let F := happrox.toOpenPartialHomeomorph f (ball 0 R) hc isOpen_ball
  have hball : ball 0 (R / 4) ⊆ F.target := by
    have h := happrox.closedBall_subset_target hc isOpen_ball
      (by positivity : 0 ≤ R / 2)
      (closedBall_subset_ball (by linarith : R / 2 < R))
    have h' : closedBall (0 : E) (R / 4) ⊆ F.target := by
      convert h using 1
      norm_num [L, hf0]
      congr 1
      ring
    exact ball_subset_closedBall.trans h'
  refine ⟨F, rfl, rfl, hball, ?_, ?_⟩
  · intro y hy
    have hx : F.symm y ∈ ball 0 R := F.map_target hy
    have hdiff := (hf.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
    obtain ⟨A, hA⟩ := isInvertible_of_norm_sub_id_le_half (hclose (F.symm y) hx)
    apply (F.contDiffAt_symm hy (f₀' := A) ?_
      (hf.contDiffAt (isOpen_ball.mem_nhds hx))).contDiffWithinAt
    simpa only [F, ApproximatesLinearOn.toOpenPartialHomeomorph_coe, hA] using hdiff.hasFDerivAt
  · have hzero : (0 : E) ∈ F.source := mem_ball_self hR
    simpa only [show F 0 = 0 from hf0] using F.left_inv hzero

end PoincareConjecture.HarmonicCoordinates
