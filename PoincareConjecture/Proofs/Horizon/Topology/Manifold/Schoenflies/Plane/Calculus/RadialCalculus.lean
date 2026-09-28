import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.RadialExtension

set_option autoImplicit false

open Set Metric Function
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem unitRadialProjection_pos_smul (q0 : sphere (0 : E) 1)
    {r : ℝ} (hr : 0 < r) (x : E) :
    unitRadialProjection q0 (r • x) = unitRadialProjection q0 x := by
  by_cases hx : x = 0
  · simp [hx]
  apply Subtype.ext
  rw [unitRadialProjection_coe_of_ne_zero q0 (smul_ne_zero hr.ne' hx),
    unitRadialProjection_coe_of_ne_zero q0 hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, mul_inv, smul_smul]
  congr 1
  calc
    (r⁻¹ * ‖x‖⁻¹) * r = (r⁻¹ * r) * ‖x‖⁻¹ := by ring
    _ = ‖x‖⁻¹ := by rw [inv_mul_cancel₀ hr.ne', one_mul]

theorem radialFamilyExtension_pos_smul {G : Type*} (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → G) (z : ℝ) {r : ℝ} (hr : 0 < r) (x : E) :
    radialFamilyExtension q0 c (z, r • x) = radialFamilyExtension q0 c (z, x) := by
  simp only [radialFamilyExtension, unitRadialProjection_pos_smul q0 hr]

theorem fderiv_apply_self_eq_zero_of_pos_smul_constant {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F} {x : E}
    (hG : DifferentiableAt ℝ G x) (hconst : ∀ r : ℝ, 0 < r → G (r • x) = G x) :
    fderiv ℝ G x x = 0 := by
  have heq : (fun t : ℝ => G (t • x)) =ᶠ[𝓝 1] (fun _ => G x) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with t ht
    exact hconst t ht
  have hc := (hasDerivAt_const (1 : ℝ) (G x)).congr_of_eventuallyEq heq
  have hd := hG.hasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ)
    ((hasDerivAt_id (1 : ℝ)).smul_const x) (by simp)
  simpa only [one_smul] using hd.unique hc

theorem fderiv_radialFamilyExtension_self {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q0 : sphere (0 : E) 1) (c : ℝ → sphere (0 : E) 1 → F) (z : ℝ) (x : E)
    (hG : DifferentiableAt ℝ (fun y => radialFamilyExtension q0 c (z, y)) x) :
    fderiv ℝ (fun y => radialFamilyExtension q0 c (z, y)) x x = 0 :=
  fderiv_apply_self_eq_zero_of_pos_smul_constant hG
    (fun _ hr => radialFamilyExtension_pos_smul q0 c z hr x)

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasFDerivAt_norm_unit (q : sphere (0 : E) 1) :
    HasFDerivAt (fun x : E => ‖x‖) (innerSL ℝ (q : E)) (q : E) := by
  have h := (hasStrictFDerivAt_norm_sq (q : E)).hasFDerivAt.sqrt
    (by simp [norm_eq_of_mem_sphere q])
  simp only [Real.sqrt_sq (norm_nonneg _), norm_eq_of_mem_sphere q, one_div] at h
  rw [← Nat.cast_smul_eq_nsmul ℝ 2 (innerSL ℝ (q : E)), smul_smul] at h
  norm_num at h
  exact h

theorem contDiffAt_unitRadialProjection_coe {m : ℕ∞ω} (q0 : sphere (0 : E) 1)
    {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ m (fun y : E => (unitRadialProjection q0 y : E)) x := by
  apply (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul
    contDiffAt_id).congr_of_eventuallyEq
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds
    (show x ∈ ({0} : Set E)ᶜ from hx)] with y hy
  exact unitRadialProjection_coe_of_ne_zero q0 hy

end InnerProduct

end Poincare.Manifold.Schoenflies.Plane
