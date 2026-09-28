import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetCollarRegularity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetPotentialStokes
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryGlobal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex InnerProductSpace
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Gauss

private theorem fderiv_log_distance {x a : LoopPlane} (hxa : x ≠ a) (w : LoopPlane) :
    fderiv ℝ (fun y : LoopPlane => Real.log ‖y - a‖) x w =
      inner ℝ (x - a) w / ‖x - a‖ ^ 2 := by
  have hn : ‖x - a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa))
  have heq : (fun y : LoopPlane => Real.log ‖y - a‖) =
      fun y => (1 / 2 : ℝ) * Real.log (‖y - a‖ ^ 2) := by
    funext y
    rw [Real.log_pow]
    norm_num
    ring
  have hh := (((hasFDerivAt_id x).sub_const a).norm_sq.log hn).const_mul (1 / 2)
  simp only [id_eq] at hh
  rw [heq, hh.fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply]
  ring

private theorem log_distance_radial_nonneg {x a : LoopPlane} (ha : ‖a‖ < ‖x‖) :
    0 ≤ fderiv ℝ (fun y : LoopPlane => Real.log ‖y - a‖) x x := by
  have hxa : x ≠ a := fun h => (lt_irrefl ‖a‖) (h ▸ ha)
  rw [fderiv_log_distance hxa]
  apply div_nonneg _ (sq_nonneg _)
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have hcs := real_inner_le_norm a x
  have hx := norm_nonneg x
  nlinarith

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Gauss

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

set_option maxHeartbeats 1400000 in

theorem exists_curvature_radial_bound (S : M65MinimalDisk g connection gamma) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let L := fun (R theta : ℝ) =>
      let z := e.symm (R • Proofs.M58.angularPoint theta)
      fderiv ℝ (fun w => Real.log (S.conformalFactor (e w))) z z / 2
    ∃ R0 : ℝ, 0 < R0 ∧ R0 < 1 ∧ ∀ R : ℝ, R0 < R → R < 1 →
      IntervalIntegrable (L R) volume (-Real.pi) Real.pi ∧
        -(∫ theta in (-Real.pi)..Real.pi, L R theta) ≤
          ∫ z in closedBall (0 : LoopPlane) R, logarithmicGaussDensity S.conformalFactor z := by
  classical
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let f := fun y : LoopPlane => Real.log (S.conformalFactor y)
  let L := fun (R theta : ℝ) =>
    let z := e.symm (R • Proofs.M58.angularPoint theta)
    fderiv ℝ (fun w => Real.log (S.conformalFactor (e w))) z z / 2
  obtain ⟨R0, hR0, hR01, hpos⟩ := S.exists_regular_annulus
  obtain ⟨B, m, v, hB, hv, hformula, hstokes⟩ := S.exists_interior_curvature_flux
  have hcenters (a : ℂ) (ha : a ∈ B) : ‖e a‖ ≤ R0 := by
    by_contra! hn
    have ha1 : ‖e a‖ < 1 := by
      change ‖orthonormalBasisOneI.repr a‖ < 1
      rw [orthonormalBasisOneI.repr.norm_map]
      exact mem_ball_zero_iff.mp ((hB a).mp ha).1
    have hp := hpos (e a) hn ha1
    rw [((hB a).mp ha).2] at hp
    exact (lt_irrefl 0) hp
  let U : Set LoopPlane := {z | R0 < ‖z‖ ∧ ‖z‖ < 1}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hsmooth (x : LoopPlane) (hx : x ∈ U) : ContDiffAt ℝ ∞ f x := by
    have hball : e.symm x ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      change ‖orthonormalBasisOneI.repr.symm x‖ < 1
      rw [orthonormalBasisOneI.repr.symm.norm_map]
      exact hx.2
    have hh := S.conformalFactor_complex_contDiffOn.contDiffAt (isOpen_ball.mem_nhds hball)
    have hc : ContDiffAt ℝ ∞ S.conformalFactor x := e.contDiffAt_comp_iff.mp hh
    exact hc.log (hpos x hx.1 hx.2).ne'
  have hlocal (x : LoopPlane) (hx : x ∈ U) :
      v =ᶠ[𝓝 x] fun y => f y / 2 - ∑ a ∈ B, (m a : ℝ) * Real.log ‖y - e a‖ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    apply hformula y (mem_ball_zero_iff.mpr hy.2)
    intro hb
    have hh := hcenters (e.symm y) hb
    rw [e.apply_symm_apply] at hh
    exact (not_lt_of_ge hh) hy.1
  have hderiv (x : LoopPlane) (hx : x ∈ U) :
      fderiv ℝ v x x = fderiv ℝ f x x / 2 -
        ∑ a ∈ B, (m a : ℝ) * fderiv ℝ (fun y : LoopPlane => Real.log ‖y - e a‖) x x := by
    have hlog (a : ℂ) (ha : a ∈ B) :
        DifferentiableAt ℝ (fun y : LoopPlane => Real.log ‖y - e a‖) x :=
      (harmonicAt_log_distance (fun h => by
        have hn := hcenters a ha
        rw [← h] at hn
        exact (not_lt_of_ge hn) hx.1)).1.differentiableAt (by norm_num)
    have hs := HasFDerivAt.fun_sum (fun a ha => (hlog a ha).hasFDerivAt.const_mul (m a : ℝ))
    have hh := (((hsmooth x hx).differentiableAt (by simp)).hasFDerivAt.mul_const
      ((2 : ℝ)⁻¹)).sub hs
    change HasFDerivAt (fun y => f y * (2 : ℝ)⁻¹ -
      ∑ a ∈ B, (m a : ℝ) * Real.log ‖y - e a‖) _ x at hh
    rw [(hlocal x hx).fderiv_eq]
    simp only [div_eq_mul_inv]
    rw [hh.fderiv]
    simp only [sub_apply, smul_apply, sum_apply, smul_eq_mul]
    ring
  refine ⟨R0, hR0, hR01, ?_⟩
  intro R hRR hR1
  have hR : 0 < R := hR0.trans hRR
  let x := fun theta => R • Proofs.M58.angularPoint theta
  have hxnorm (theta : ℝ) : ‖x theta‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, Proofs.M58.norm_angularPoint, mul_one]
  have hxU (theta : ℝ) : x theta ∈ U := by
    change R0 < ‖x theta‖ ∧ ‖x theta‖ < 1
    rw [hxnorm]
    exact ⟨hRR, hR1⟩
  have hLC : Continuous (L R) := S.radial_log_flux_continuous hR hR1
    (fun z hz => hpos z (hz ▸ hRR) (hz ▸ hR1))
  have hVC : Continuous (fun theta =>
      fderiv ℝ v (x theta) (Proofs.M58.angularPoint theta)) := by
    have hDf := (hv.fderiv_of_isOpen isOpen_ball (m := 0) (by norm_num)).continuousOn
    have hxC : Continuous x := Proofs.M58.contDiff_angularPoint.continuous.const_smul R
    have hcomp : Continuous (fun theta => fderiv ℝ v (x theta)) :=
      hDf.comp_continuous hxC (fun theta => mem_ball_zero_iff.mpr ((hxnorm theta) ▸ hR1))
    exact hcomp.clm_apply Proofs.M58.contDiff_angularPoint.continuous
  have hpoint (theta : ℝ) : -L R theta ≤
      -R * fderiv ℝ v (x theta) (Proofs.M58.angularPoint theta) := by
    have hc := ((hsmooth (x theta) (hxU theta)).differentiableAt (by simp)).hasFDerivAt
    have hc' : HasFDerivAt f (fderiv ℝ f (x theta)) (e (e.symm (x theta))) := by
      simpa only [e.apply_symm_apply] using hc
    have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A (e.symm (x theta)))
      (hc'.comp (e.symm (x theta)) e.hasFDerivAt).fderiv
    have hL : L R theta = fderiv ℝ f (x theta) (x theta) / 2 := by
      change fderiv ℝ (f ∘ e) (e.symm (x theta)) (e.symm (x theta)) / 2 = _
      rw [he, ContinuousLinearMap.comp_apply]
      change fderiv ℝ f (x theta) (e (e.symm (x theta))) / 2 = _
      rw [e.apply_symm_apply]
    have hsum : 0 ≤ ∑ a ∈ B, (m a : ℝ) *
        fderiv ℝ (fun y : LoopPlane => Real.log ‖y - e a‖) (x theta) (x theta) := by
      exact Finset.sum_nonneg (fun a ha => mul_nonneg (Nat.cast_nonneg _)
        (log_distance_radial_nonneg ((hcenters a ha).trans_lt ((hxnorm theta).symm ▸ hRR))))
    have hvx := hderiv (x theta) (hxU theta)
    have hvscale : fderiv ℝ v (x theta) (x theta) =
        R * fderiv ℝ v (x theta) (Proofs.M58.angularPoint theta) := by
      exact (fderiv ℝ v (x theta)).map_smul R (Proofs.M58.angularPoint theta)
    rw [hL]
    rw [hvscale] at hvx
    linarith
  have hle := intervalIntegral.integral_mono_on (μ := volume) (a := -Real.pi) (b := Real.pi)
    (f := fun theta => -L R theta)
    (g := fun theta => -R * fderiv ℝ v (x theta) (Proofs.M58.angularPoint theta))
    (by linarith [Real.pi_pos]) (hLC.neg.intervalIntegrable _ _)
    ((hVC.const_mul (-R)).intervalIntegrable _ _) (fun theta _ => hpoint theta)
  have hs := (hstokes R hR hR1).2
  change (∫ z in closedBall (0 : LoopPlane) R, logarithmicGaussDensity S.conformalFactor z) =
    -R * ∫ theta in (-Real.pi)..Real.pi,
      fderiv ℝ v (x theta) (Proofs.M58.angularPoint theta) at hs
  refine ⟨hLC.intervalIntegrable _ _, ?_⟩
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hle
  exact hle.trans_eq hs.symm

end PoincareConjecture.M65MinimalDisk
