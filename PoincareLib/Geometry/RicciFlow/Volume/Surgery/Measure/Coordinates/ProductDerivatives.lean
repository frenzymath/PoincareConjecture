import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
Adapted from Mapher `PoincareMT/Proofs/M10/ProductDerivatives.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Horizontal and time derivatives of actual product functions

These chain-rule identities compare genuine derivatives of the slices with
the full derivative. They do not infer differentiability from totalized
derivative expressions.
-/

set_option autoImplicit false

namespace PoincareMT.SurgeryVolume.Measure

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The horizontal total derivative is the derivative of the fixed-time slice. -/
theorem fderiv_horizontal_eq {f : X × ℝ → Y} {z : X × ℝ}
    (hf : DifferentiableAt ℝ f z) (h : X) :
    fderiv ℝ f z (h, 0) = fderiv ℝ (fun x ↦ f (x, z.2)) z.1 h := by
  have hc := hf.hasFDerivAt.comp (f := fun x : X ↦ (x, z.2)) z.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  change fderiv ℝ f z (h, 0) = fderiv ℝ (f ∘ fun x : X ↦ (x, z.2)) z.1 h
  rw [hc.fderiv]
  rfl

/-- Holding the initial vector fixed gives the full derivative in the time direction. -/
theorem hasDerivAt_time_slice {f : X × ℝ → Y} {z : X × ℝ}
    (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun t ↦ f (z.1, t)) (fderiv ℝ f z (0, 1)) z.2 := by
  exact hf.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))

end PoincareMT.SurgeryVolume.Measure
