import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Prod








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasDerivAt_spatialDerivative_time (G : ℝ × E → V) (s : ℝ) (y v : E)
    (hG : ContDiffAt ℝ ∞ G (s, y)) :
    HasDerivAt (fun r ↦ fderiv ℝ G (r, y) (0, v))
      (fderiv ℝ (fun x ↦ fderiv ℝ G (s, x) (1, 0)) y v) s := by
  have hDG : DifferentiableAt ℝ (fderiv ℝ G) (s, y) :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have htime : HasDerivAt (fun r ↦ fderiv ℝ G (r, y) (0, v))
      (fderiv ℝ (fderiv ℝ G) (s, y) (1, 0) (0, v)) s := by
    simpa using (hDG.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))).clm_apply
        (hasDerivAt_const s ((0, v) : ℝ × E))
  have hspace := (hDG.hasFDerivAt.comp y
    ((hasFDerivAt_const s y).prodMk (hasFDerivAt_id y))).clm_apply
      (hasFDerivAt_const ((1, 0) : ℝ × E) y)
  have hvalue : fderiv ℝ (fun x ↦ fderiv ℝ G (s, x) (1, 0)) y v =
      fderiv ℝ (fderiv ℝ G) (s, y) (0, v) (1, 0) := by
    simpa using congrArg (fun L : E →L[ℝ] V ↦ L v) hspace.fderiv
  have htwo : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  rw [(hG.isSymmSndFDerivAt (by simpa using htwo)) ((1, 0) : ℝ × E) (0, v)] at htime
  exact htime.congr_deriv hvalue.symm

end PoincareConjecture.Proofs.M09
