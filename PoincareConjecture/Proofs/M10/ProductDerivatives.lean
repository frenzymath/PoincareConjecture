import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

namespace PoincareConjecture.M10

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem fderiv_horizontal_eq {f : X × ℝ → Y} {z : X × ℝ}
    (hf : DifferentiableAt ℝ f z) (h : X) :
    fderiv ℝ f z (h, 0) = fderiv ℝ (fun x ↦ f (x, z.2)) z.1 h := by
  have hc := hf.hasFDerivAt.comp (f := fun x : X ↦ (x, z.2)) z.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  change fderiv ℝ f z (h, 0) = fderiv ℝ (f ∘ fun x : X ↦ (x, z.2)) z.1 h
  rw [hc.fderiv]
  rfl

theorem hasDerivAt_time_slice {f : X × ℝ → Y} {z : X × ℝ}
    (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun t ↦ f (z.1, t)) (fderiv ℝ f z (0, 1)) z.2 := by
  exact hf.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))

end PoincareConjecture.M10
