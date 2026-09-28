import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyPolar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric Complex
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem continuous_cauchyPolarField {ψ : ℂ → E} (hψ : ContDiff ℝ 1 ψ)
    {v : ℝ → ℂ} (hv : Continuous v) :
    Continuous (fun p : ℝ × ℝ => fderiv ℝ ψ (circleMap 0 p.1 p.2) (v p.2)) := by
  have hc : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    unfold circleMap
    fun_prop
  exact ((hψ.continuous_fderiv one_ne_zero).comp hc).clm_apply (hv.comp continuous_snd)

theorem integral_cauchyPolarRadial [CompleteSpace E] {ψ : ℂ → E}
    (hψ : ContDiff ℝ 1 ψ) (R θ : ℝ) :
    (∫ r in (0 : ℝ)..R, fderiv ℝ ψ (circleMap 0 r θ) (circleMap 0 1 θ)) =
      ψ (circleMap 0 R θ) - ψ 0 := by
  have hc (r : ℝ) : HasDerivAt (fun s : ℝ => circleMap 0 s θ) (circleMap 0 1 θ) r := by
    simpa only [circleMap, zero_add, ofReal_one, one_mul, ofRealCLM_apply] using
      (ofRealCLM.hasDerivAt (x := r)).mul_const (Complex.exp (θ * I))
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ => ψ (circleMap 0 s θ))
      (fderiv ℝ ψ (circleMap 0 r θ) (circleMap 0 1 θ)) r :=
    ((hψ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r (hc r))
  have hi : IntervalIntegrable
      (fun r : ℝ => fderiv ℝ ψ (circleMap 0 r θ) (circleMap 0 1 θ)) volume 0 R :=
    ((continuous_cauchyPolarField hψ (v := fun _ => circleMap 0 1 θ) continuous_const).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 R
  simpa only [circleMap_zero_radius, Function.const_apply] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi

theorem integral_cauchyPolarAngular [CompleteSpace E] {ψ : ℂ → E}
    (hψ : ContDiff ℝ 1 ψ) {r : ℝ} (hr : 0 < r) :
    (∫ θ in (-Real.pi)..Real.pi,
      I • fderiv ℝ ψ (circleMap 0 r θ) (I * circleMap 0 1 θ)) = 0 := by
  let Y := fun θ : ℝ => I • fderiv ℝ ψ (circleMap 0 r θ) (I * circleMap 0 1 θ)
  have hY : Continuous Y :=
    ((continuous_cauchyPolarField hψ
      ((continuous_circleMap 0 1).const_mul I)).comp
        (continuous_const.prodMk continuous_id)).const_smul I
  have hd (θ : ℝ) : HasDerivAt (fun t : ℝ => I • ψ (circleMap 0 r t)) (r • Y θ) θ := by
    have h := ((hψ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap 0 r θ)).const_smul I
    change HasDerivAt (fun t : ℝ => I • ψ (circleMap 0 r t))
      (I • fderiv ℝ ψ (circleMap 0 r θ) (circleMap 0 r θ * I)) θ at h
    have he : circleMap 0 r θ * I = r • (I * circleMap 0 1 θ) := by
      simp only [circleMap, zero_add, ofReal_one, one_mul, real_smul]
      ring
    rw [he, map_smul, smul_comm] at h
    exact h
  have heq : circleMap 0 r Real.pi = circleMap 0 r (-Real.pi) := by simp [circleMap]
  have hzero : (∫ θ in (-Real.pi)..Real.pi, r • Y θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
      ((continuous_const.smul hY).intervalIntegrable _ _), heq, sub_self]
  rw [intervalIntegral.integral_smul] at hzero
  exact (smul_eq_zero.mp hzero).resolve_left hr.ne'

end PoincareConjecture.M65Branch
