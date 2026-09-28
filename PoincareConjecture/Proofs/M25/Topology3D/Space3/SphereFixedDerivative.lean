import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereTangency
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach











set_option autoImplicit false

open Set Filter
open scoped Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem fderiv_eq_of_local_fixed_sphere (f : E → E) (x v : E) (hx : ‖x‖ = 1)
    (hf : DifferentiableAt ℝ f x)
    (hfixed : ∀ᶠ y in 𝓝 x, ‖y‖ = 1 → f y = y)
    (hv : ⟪x, v⟫_ℝ = 0) : fderiv ℝ f x v = v := by
  obtain ⟨γ, hγ0, hγ, hγsphere⟩ := exists_sphere_curve_with_velocity x v hx hv
  have hF : HasFDerivAt f (fderiv ℝ f x) (γ 0) := by
    rw [hγ0]
    exact hf.hasFDerivAt
  have hcont : Tendsto γ (𝓝 0) (𝓝 x) := by
    simpa only [hγ0] using hγ.continuousAt.tendsto
  have heq : (fun t => f (γ t)) =ᶠ[𝓝 0] γ := by
    filter_upwards [hcont.eventually hfixed, hγsphere] with t ht hs
    exact ht hs
  exact (hF.comp_hasDerivAt 0 hγ).unique (hγ.congr_of_eventuallyEq heq)



theorem fixedHyperplane_interpolation_injective (A : E →L[ℝ] E) (x : E)
    (hx : ‖x‖ = 1) (hA : ∀ v, ⟪x, v⟫_ℝ = 0 → A v = v)
    (hn : 0 < ⟪x, A x⟫_ℝ) {a : ℝ} (ha : a ∈ Icc 0 1) :
    Function.Injective ((1 - a) • ContinuousLinearMap.id ℝ E + a • A) := by
  have hxx : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have hnormal (v : E) : ⟪x, A v⟫_ℝ = ⟪x, A x⟫_ℝ * ⟪x, v⟫_ℝ := by
    have hv : ⟪x, v - ⟪x, v⟫_ℝ • x⟫_ℝ = 0 := by
      simp only [inner_sub_right, inner_smul_right, hxx, mul_one, sub_self]
    have h := congrArg (fun w => ⟪x, w⟫_ℝ) (hA _ hv)
    simp only [map_sub, map_smul, inner_sub_right, inner_smul_right, hxx] at h
    nlinarith
  have hpos : 0 < 1 - a + a * ⟪x, A x⟫_ℝ := by
    by_cases ha0 : a = 0
    · simp only [ha0, sub_zero, zero_mul, add_zero, zero_lt_one]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ha.2)
        (mul_pos (lt_of_le_of_ne ha.1 (Ne.symm ha0)) hn)
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  change (1 - a) • v + a • A v = 0 at hv
  have hnv := congrArg (fun w => ⟪x, w⟫_ℝ) hv
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hnv
  rw [hnormal v] at hnv
  have hz : ⟪x, v⟫_ℝ = 0 := by
    have hp : (1 - a + a * ⟪x, A x⟫_ℝ) * ⟪x, v⟫_ℝ = 0 := by nlinarith [hnv]
    exact (mul_eq_zero.mp hp).resolve_left hpos.ne'
  simpa only [hA v hz, ← add_smul, sub_add_cancel, one_smul] using hv



theorem fixedHyperplane_interpolation_isUnit [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (x : E) (hx : ‖x‖ = 1)
    (hA : ∀ v, ⟪x, v⟫_ℝ = 0 → A v = v) (hn : 0 < ⟪x, A x⟫_ℝ)
    {a : ℝ} (ha : a ∈ Icc 0 1) :
    IsUnit ((1 - a) • ContinuousLinearMap.id ℝ E + a • A) := by
  have hi := fixedHyperplane_interpolation_injective A x hx hA hn ha
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    rfl).mp hi⟩

end PoincareConjecture.M25.Topology3D
