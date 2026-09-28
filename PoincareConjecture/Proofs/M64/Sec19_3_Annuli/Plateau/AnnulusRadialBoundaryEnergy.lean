import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialAffineFilling













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => ball (0 : LoopPlane) 1



theorem m64Periodic_contDiff_deriv_bound {c : ℝ → E}
    (hc : ContDiff ℝ 1 c) (hP : Function.Periodic c curvePeriod) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖deriv c x‖ ≤ D := by
  have hdP : Function.Periodic (deriv c) curvePeriod := by
    intro x
    have heq : (fun y => c (y + curvePeriod)) = c := funext hP
    have h := deriv_comp_add_const (f := c) (a := curvePeriod) (x := x)
    rw [heq] at h
    exact h.symm
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) curvePeriod) (hc.continuous_deriv (by simp)).continuousOn
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro x
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  let y := toIcoMod hperiod 0 x
  have hy : y ∈ Icc (0 : ℝ) curvePeriod := Ico_subset_Icc_self (toIcoMod_mem_Ico' hperiod x)
  have heq : deriv c y = deriv c x := by
    simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
      (hdP.zsmul (-toIcoDiv hperiod 0 x)) x
  rw [← heq]
  exact (hD y hy).trans (le_max_left _ _)



theorem m64RadialBoundaryPlane_column {c : ℝ → E} (hc : ContDiff ℝ 1 c)
    (a : LoopPlane) (r : ℝ) (z : LoopPlane) (i : Fin 2) :
    fderiv ℝ (fun y : LoopPlane => c ((a + r • y) 0)) z (EuclideanSpace.single i 1) =
      (r * (EuclideanSpace.single i (1 : ℝ)) 0) • deriv c ((a + r • z) 0) := by
  let P := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
  have hbase (q : LoopPlane) :
      fderiv ℝ (fun y : LoopPlane => c (y 0)) q (EuclideanSpace.single i 1) =
        (EuclideanSpace.single i (1 : ℝ)) 0 • deriv c (q 0) := by
    have hd := (hc.differentiable (by simp) (q 0)).hasFDerivAt.comp q P.hasFDerivAt
    simpa +instances only [Function.comp_def, P, EuclideanSpace.coe_proj,
      ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv] using!
        congrArg (fun D => D (EuclideanSpace.single i 1)) hd.fderiv
  have hrescale := congrArg (fun D => D (EuclideanSpace.single i 1))
    (M60.suRescale_fderiv (fun y : LoopPlane => c (y 0)) a r z)
  simpa only [smul_apply, hbase, smul_smul] using hrescale



theorem m64RadialBoundaryPlane_energy_bound {c : ℝ → E}
    (hc : ContDiff ℝ 1 c) (hP : Function.Periodic c curvePeriod) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : LoopPlane) (r : ℝ),
      (∫ z in S, ‖fderiv ℝ (fun y : LoopPlane => c ((a + r • y) 0)) z
        (EuclideanSpace.single (0 : Fin 2) 1)‖ ^ 2) +
        (∫ z in S, ‖fderiv ℝ (fun y : LoopPlane => c ((a + r • y) 0)) z
          (EuclideanSpace.single (1 : Fin 2) 1)‖ ^ 2) ≤ C * r ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := m64Periodic_contDiff_deriv_bound hc hP
  refine ⟨(volume S).toReal * D ^ 2, by positivity, ?_⟩
  intro a r
  have h0 (z : LoopPlane) :
      fderiv ℝ (fun y : LoopPlane => c ((a + r • y) 0)) z
        (EuclideanSpace.single (0 : Fin 2) 1) = r • deriv c ((a + r • z) 0) := by
    simpa only [PiLp.single_apply, if_true, mul_one] using m64RadialBoundaryPlane_column hc a r z 0
  have h1 (z : LoopPlane) :
      fderiv ℝ (fun y : LoopPlane => c ((a + r • y) 0)) z
        (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
    simpa only [PiLp.single_apply, show (0 : Fin 2) ≠ 1 from by decide, if_false,
      mul_zero, zero_smul] using m64RadialBoundaryPlane_column hc a r z 1
  simp_rw [h1, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero, add_zero, h0]
  have hcont : Continuous (fun z : LoopPlane => ‖r • deriv c ((a + r • z) 0)‖ ^ 2) := by
    exact (((hc.continuous_deriv (by simp)).comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp
        (continuous_const.add (continuous_id.const_smul r)))).const_smul r).norm.pow 2
  calc
    _ ≤ ∫ _ in S, r ^ 2 * D ^ 2 := by
      apply integral_mono
        (hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : LoopPlane) 1)
          |>.mono_set ball_subset_closedBall)
        (continuous_const.continuousOn.integrableOn_compact
          (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall)
      intro z
      change ‖r • deriv c ((a + r • z) 0)‖ ^ 2 ≤ r ^ 2 * D ^ 2
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) hD).mpr (hbound _)) (sq_nonneg r)
    _ = _ := by rw [setIntegral_const, smul_eq_mul, Measure.real]; ring

end PoincareConjecture
