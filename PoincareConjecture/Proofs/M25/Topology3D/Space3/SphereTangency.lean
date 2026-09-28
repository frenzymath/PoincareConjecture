import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open Set Filter
open scoped Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem exists_sphere_curve_with_velocity (x v : E) (hx : ‖x‖ = 1)
    (hv : ⟪x, v⟫_ℝ = 0) :
    ∃ γ : ℝ → E, γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ), ‖γ t‖ = 1 := by
  let raw : ℝ → E := fun t => x + t • v
  have hraw0 : raw 0 = x := by simp only [raw, zero_smul, add_zero]
  have hraw : HasDerivAt raw v 0 := by
    simpa only [raw, one_smul, zero_add, id_eq] using
      (hasDerivAt_const (0 : ℝ) x).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hn0 : ‖raw 0‖ ≠ 0 := by rw [hraw0, hx]; exact one_ne_zero
  have hrawne : raw 0 ≠ 0 := norm_ne_zero_iff.mp hn0
  have hsq : HasDerivAt (fun t => ‖raw t‖ ^ 2) 0 0 := by
    simpa only [hraw0, hv, mul_zero] using hraw.norm_sq
  have hn : HasDerivAt (fun t => ‖raw t‖) 0 0 := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, zero_div] using
      hsq.sqrt (pow_ne_zero 2 hn0)
  have hinv : HasDerivAt (fun t => ‖raw t‖⁻¹) 0 0 := by
    simpa only [neg_zero, zero_div] using hn.fun_inv hn0
  refine ⟨fun t => NormedSpace.normalize (raw t), ?_, ?_, ?_⟩
  · simp only [NormedSpace.normalize, hraw0, hx, inv_one, one_smul]
  · simpa only [NormedSpace.normalize, hraw0, hx, inv_one, zero_smul, one_smul, add_zero] using
      hinv.fun_smul hraw
  · filter_upwards [hraw.continuousAt.eventually (eventually_ne_nhds hrawne)] with t ht
    exact NormedSpace.norm_normalize ht

theorem inner_fderiv_eq_zero_of_local_sphere (f : E → F) (x v : E) (hx : ‖x‖ = 1)
    (hf : DifferentiableAt ℝ f x)
    (hboundary : ∀ᶠ y in 𝓝 x, ‖y‖ = 1 → ‖f y‖ = 1)
    (hv : ⟪x, v⟫_ℝ = 0) : ⟪f x, fderiv ℝ f x v⟫_ℝ = 0 := by
  obtain ⟨γ, hγ0, hγ, hγsphere⟩ := exists_sphere_curve_with_velocity x v hx hv
  have hF : HasFDerivAt f (fderiv ℝ f x) (γ 0) := by
    rw [hγ0]
    exact hf.hasFDerivAt
  have hd : HasDerivAt (fun t => ‖f (γ t)‖ ^ 2) (2 * ⟪f x, fderiv ℝ f x v⟫_ℝ) 0 := by
    simpa only [Function.comp_def, hγ0] using (hF.comp_hasDerivAt 0 hγ).norm_sq
  have hcont : Tendsto γ (𝓝 0) (𝓝 x) := by
    simpa only [hγ0] using hγ.continuousAt.tendsto
  have heq : (fun t => ‖f (γ t)‖ ^ 2) =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
    filter_upwards [hcont.eventually hboundary, hγsphere] with t ht hs
    rw [ht hs, one_pow]
  have hzero := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq heq
  have hderiv := hd.unique hzero
  linarith

end PoincareConjecture.M25.Topology3D
