import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CoframeEquation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]



theorem christoffelBilinear_radial_eq_zero_of_gauss
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ ∞ B)
    (hinv : ∀ y, (B y).IsInvertible)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hgauss : ∀ x w, B x x w = inner ℝ x w) (x : E) (t : ℝ) :
    christoffelBilinear B (t • x) x x = 0 := by
  have hd (y d w : E) : fderiv ℝ B y d y w + B y d w = inner ℝ d w := by
    have h := (((hB.differentiable (by simp)).differentiableAt.hasFDerivAt.clm_apply
      (hasFDerivAt_id y)).clm_apply (hasFDerivAt_const w y)).fderiv
    have heq : (fun z => B z z w) = (innerSL ℝ).flip w := funext fun z => hgauss z w
    simp only [id_eq] at h
    rw [heq, ContinuousLinearMap.fderiv] at h
    have hh := congrArg (fun L => L d) h
    simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add,
      innerSL_apply_apply, add_comm] using hh.symm
  have hd_symm (y d v w : E) : fderiv ℝ B y d v w = fderiv ℝ B y d w v := by
    have happ (v w : E) : fderiv ℝ (fun z => B z v w) y d = fderiv ℝ B y d v w := by
      have h := (((hB.differentiable (by simp)).differentiableAt.hasFDerivAt.clm_apply
        (hasFDerivAt_const v y)).clm_apply (hasFDerivAt_const w y)).fderiv
      simpa only [ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply] using congrArg (fun L => L d) h
    rw [← happ v w, ← happ w v]
    exact congrArg (fun L => L d) (congrArg (fun f => fderiv ℝ f y)
      (funext fun z => hsymm z v w))
  have hdiag (y : E) : christoffelBilinear B y y y = 0 := by
    have h1 (w : E) : fderiv ℝ B y y y w = 0 := by
      have h := hd y y w
      rw [hgauss] at h
      linarith
    have h2 (w : E) : fderiv ℝ B y w y y = 0 := by
      have h := hd y w y
      rw [hsymm y w y, hgauss, real_inner_comm y w] at h
      linarith
    change (B y).inverse (metricKoszulCovector (fderiv ℝ B y) y y) = 0
    have hk : metricKoszulCovector (fderiv ℝ B y) y y = 0 := by
      ext w
      simp only [metricKoszulCovector, smul_apply, add_apply, sub_apply,
        ContinuousLinearMap.flip_apply, smul_eq_mul, zero_apply]
      rw [hd_symm y y w y, h1, h2]
      ring
    rw [hk, map_zero]
  have hc : Continuous (fun s : ℝ => christoffelBilinear B (s • x) x x) := by
    have hΓ : Continuous (christoffelBilinear B) := continuous_iff_continuousAt.mpr
      (fun y => (contDiffAt_christoffelBilinear hB.contDiffAt (hinv y)).continuousAt)
    exact ((hΓ.comp (continuous_id.smul continuous_const)).clm_apply
      continuous_const).clm_apply continuous_const
  have heq : (fun s : ℝ => christoffelBilinear B (s • x) x x) = fun _ => 0 := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hc continuous_const
    intro s hs
    have hs0 : s ≠ 0 := hs
    have h := hdiag (s • x)
    simp only [map_smul, smul_apply] at h
    exact (smul_eq_zero.mp (smul_eq_zero.mp h |>.resolve_left hs0)).resolve_left hs0
  exact congrFun heq t

end PoincareConjecture.CoordinateExponential
