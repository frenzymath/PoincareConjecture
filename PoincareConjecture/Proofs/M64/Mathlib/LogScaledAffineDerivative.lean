import Mathlib.Analysis.SpecialFunctions.Log.Deriv





noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Filter
open scoped Topology

namespace PoincareConjecture.M64





theorem log_scaled_affine_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (a : F) {c : ℝ} (hc : c ≠ 0)
    {rho : F → ℝ} {lam : E → ℝ} {z : E}
    (hrho : DifferentiableAt ℝ rho (a + e z)) (hpos : rho (a + e z) ≠ 0)
    (heq : lam =ᶠ[𝓝 z] fun w => c * rho (a + e w)) (v : E) :
    fderiv ℝ (fun w => Real.log (lam w)) z v =
      fderiv ℝ (fun p => Real.log (rho p)) (a + e z) (e v) := by
  have hP : HasFDerivAt (fun w => a + e w) e.toContinuousLinearMap z :=
    e.hasFDerivAt.const_add a
  have hnear : ∀ᶠ w in 𝓝 z, rho (a + e w) ≠ 0 :=
    (hrho.continuousAt.comp (f := fun w => a + e w) hP.continuousAt).eventually_ne hpos
  have hlog : (fun w => Real.log (lam w)) =ᶠ[𝓝 z]
      fun w => Real.log c + Real.log (rho (a + e w)) := by
    filter_upwards [heq, hnear] with w hw hne
    rw [hw, Real.log_mul hc hne]
  have hd := ((hrho.hasFDerivAt.log hpos).comp z hP).const_add (Real.log c)
  change HasFDerivAt (fun w => Real.log c + Real.log (rho (a + e w))) _ z at hd
  rw [hlog.fderiv_eq, hd.fderiv, (hrho.hasFDerivAt.log hpos).fderiv]
  rfl

end PoincareConjecture.M64
