import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries










set_option autoImplicit false

namespace PoincareConjecture.M44

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem norm_iteratedFDeriv_zero_sub (f g : E → F) (x : E) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g x‖ = ‖f x - g x‖ := by
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]



theorem norm_iteratedFDeriv_fderiv_sub (m : ℕ) (f g : E → F) (x : E) :
    ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ g) x‖ =
      ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) g x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  let L := (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
  change ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ g) x‖ =
    ‖L (iteratedFDeriv ℝ m (fderiv ℝ f) x) - L (iteratedFDeriv ℝ m (fderiv ℝ g) x)‖
  rw [← L.map_sub, L.norm_map]



theorem norm_fderiv_sub_eq_jet (f g : E → F) (x : E) :
    ‖fderiv ℝ f x - fderiv ℝ g x‖ =
      ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 g x‖ := by
  rw [← norm_iteratedFDeriv_zero_sub (fderiv ℝ f) (fderiv ℝ g) x,
    norm_iteratedFDeriv_fderiv_sub]

end PoincareConjecture.M44
