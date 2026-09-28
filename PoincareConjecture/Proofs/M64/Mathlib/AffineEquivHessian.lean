import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareConjecture.M64

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fderiv2_comp_affine_equiv (f : F → G) (e : E ≃L[ℝ] F)
    (a : F) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun z => f (a + e z))) x v w =
      fderiv ℝ (fderiv ℝ f) (a + e x) (e v) (e w) := by
  have h := e.iteratedFDerivWithin_comp_right (fun z => f (a + z))
    uniqueDiffOn_univ (mem_univ (e x)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ, iteratedFDeriv_comp_add_left] at h
  have hh := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) G =>
    T ![v, w]) h
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply, ContinuousLinearEquiv.coe_coe,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Function.comp_def] using hh

end PoincareConjecture.M64
