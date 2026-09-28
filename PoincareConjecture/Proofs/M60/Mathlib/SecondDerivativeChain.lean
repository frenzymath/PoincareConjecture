import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

open Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M60

variable {P Q E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_column {u : P → E} {z : P} (hu : ContDiffAt ℝ 2 u z) (v w : P) :
    fderiv ℝ (fun q => fderiv ℝ u q w) z v = fderiv ℝ (fderiv ℝ u) z v w := by
  rw [fderiv_clm_apply
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp))
    (differentiableAt_const w)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]

theorem second_fderiv_comp {u : Q → E} {φ : P → Q} {z : P}
    (hu : ContDiffAt ℝ 2 u (φ z)) (hφ : ContDiffAt ℝ 2 φ z) (v w : P) :
    fderiv ℝ (fderiv ℝ (u ∘ φ)) z v w =
      fderiv ℝ (fderiv ℝ u) (φ z) (fderiv ℝ φ z v) (fderiv ℝ φ z w) +
        fderiv ℝ u (φ z) (fderiv ℝ (fderiv ℝ φ) z v w) := by
  have hud := hu.differentiableAt (by simp)
  have hφd := hφ.differentiableAt (by simp)
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hdφ := (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have he : (fun q => fderiv ℝ (u ∘ φ) q w) =ᶠ[𝓝 z]
      (fun q => fderiv ℝ u (φ q) (fderiv ℝ φ q w)) := by
    filter_upwards [hφ.eventually (by norm_num),
      hφ.continuousAt.eventually (hu.eventually (by norm_num))] with q hq hqu
    rw [fderiv_comp q (hqu.differentiableAt (by simp))
      (hq.differentiableAt (by simp))]
    rfl
  have hc := (hdu.hasFDerivAt.comp z hφd.hasFDerivAt).clm_apply
    (hdφ.hasFDerivAt.clm_apply (hasFDerivAt_const w z))
  change HasFDerivAt (fun q => fderiv ℝ u (φ q) (fderiv ℝ φ q w)) _ z at hc
  rw [← fderiv_column (hu.comp z hφ) v w, he.fderiv_eq, hc.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add]
  exact add_comm _ _

end PoincareConjecture.M60
