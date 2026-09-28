import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.DividedDifferences
import Mathlib.Analysis.Convex.Star












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]



def radialPrimitive (omega : E → E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∫ t in (0 : ℝ)..1, omega (t • x) x



theorem radialPrimitive_contDiff {omega : E → E →L[ℝ] ℝ}
    (homega : ContDiff ℝ ∞ omega) : ContDiff ℝ ∞ (radialPrimitive omega) := by
  exact Poincare.Analysis.contDiff_parameter_intervalIntegral_of_contDiff
    ((homega.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_fst) 0 1




theorem hasFDerivAt_radialPrimitive {omega : E → E →L[ℝ] ℝ}
    (homega : ContDiff ℝ ∞ omega) {S : Set E} (hS : StarConvex ℝ 0 S)
    (hclosed : ∀ x ∈ S, ∀ v w, fderiv ℝ omega x v w = fderiv ℝ omega x w v)
    {x : E} (hx : x ∈ S) : HasFDerivAt (radialPrimitive omega) (omega x) x := by
  let F : E × ℝ → ℝ := fun p => omega (p.2 • p.1) p.1
  have hF : ContDiff ℝ ∞ F :=
    (homega.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_fst
  let D : ℝ → E →L[ℝ] ℝ :=
    fun t => (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D :=
    ((hF.fderiv_right (m := 0) (by simp)).clm_comp contDiff_const).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hparam := Poincare.Analysis.hasFDerivAt_parameter_intervalIntegral_of_contDiff hF 0 1 x
  have hcoeff (t : ℝ) (v : E) :
      D t v = omega (t • x) v + t * (fderiv ℝ omega (t • x) v x) := by
    have h1 : HasFDerivAt (fun y => F (y, t)) (D t) x := by
      simpa only [D, Function.comp_def] using!
        ((hF.differentiable (by simp)) (x, t)).hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
    have h2 := (((homega.differentiable (by simp)) (t • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul t)).clm_apply (hasFDerivAt_id x)
    have h := congrArg (fun L : E →L[ℝ] ℝ => L v) (h1.unique h2)
    simpa only [D, Function.comp_def, id_eq, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, map_smul,
      smul_apply, smul_eq_mul] using! h
  have hEq : (∫ t in (0 : ℝ)..1, D t) = omega x := by
    ext v
    rw [ContinuousLinearMap.intervalIntegral_apply (hD.intervalIntegrable 0 1)]
    have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun s => s * omega (s • x) v) (D t v) t := by
      have hs := ((homega.differentiable (by simp)) (t • x)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const x)
      have ha := hs.clm_apply (hasDerivAt_const t v)
      have h := (hasDerivAt_id t).mul ha
      have htS := hS.smul_mem hx ht.1 ht.2
      simpa only [Function.comp_def, id_eq, Pi.mul_def, one_smul,
        map_zero, add_zero, one_mul, hcoeff,
        hclosed (t • x) htS v x] using! h
    have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hpath t (by simpa only [uIcc_of_le zero_le_one] using ht))
      ((hD.clm_apply continuous_const).intervalIntegrable 0 1)
    simpa only [one_smul, one_mul, zero_mul, sub_zero] using hI
  change HasFDerivAt (radialPrimitive omega) (∫ t in (0 : ℝ)..1, D t) x at hparam
  rwa [hEq] at hparam

end PoincareConjecture.M60

end
