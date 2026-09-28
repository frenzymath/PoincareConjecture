import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare.Manifold.Schoenflies.Hemisphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  {v : E}

abbrev Plane (v : E) := (Real ∙ v)ᗮ

theorem inner_add_center (hv : ‖v‖ = 1) (x : Plane v) :
    ⟪v, (x : E) + v⟫ = 1 := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  simp [inner_add_right, hx, hv]

theorem add_center_ne_zero (hv : ‖v‖ = 1) (x : Plane v) : (x : E) + v ≠ 0 := by
  intro h
  have := inner_add_center hv x
  rw [h, inner_zero_right] at this
  exact zero_ne_one this

def toSphere (hv : ‖v‖ = 1) (x : Plane v) : sphere (0 : E) 1 :=
  ⟨‖(x : E) + v‖⁻¹ • ((x : E) + v), by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [norm_ne_zero_iff.mpr (add_center_ne_zero hv x)]⟩

def fromSphere (v : E) (p : sphere (0 : E) 1) : Plane v :=
  (⟪v, (p : E)⟫)⁻¹ • (Plane v).orthogonalProjectionOnto (p : E)

theorem inner_toSphere (hv : ‖v‖ = 1) (x : Plane v) :
    ⟪v, (toSphere hv x : E)⟫ = ‖(x : E) + v‖⁻¹ := by
  simp only [toSphere, inner_smul_right, inner_add_center hv, mul_one]

theorem toSphere_mem_hemisphere (hv : ‖v‖ = 1) (x : Plane v) :
    0 < ⟪v, (toSphere hv x : E)⟫ := by
  rw [inner_toSphere]
  exact inv_pos.mpr (norm_pos_iff.mpr (add_center_ne_zero hv x))

theorem fromSphere_toSphere (hv : ‖v‖ = 1) (x : Plane v) :
    fromSphere v (toSphere hv x) = x := by
  rw [fromSphere, inner_toSphere, inv_inv]
  simp only [toSphere, map_smul, map_add,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    add_zero, smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (add_center_ne_zero hv x)), one_smul]

theorem toSphere_fromSphere (hv : ‖v‖ = 1) (p : sphere (0 : E) 1)
    (hp : 0 < ⟪v, (p : E)⟫) : toSphere hv (fromSphere v p) = p := by
  have hsplit : (p : E) = ⟪v, (p : E)⟫ • v +
      ((Plane v).orthogonalProjectionOnto (p : E) : E) := by
    nth_rw 1 [← ((Real ∙ v).starProjection_add_starProjection_orthogonal (p : E))]
    rw [Submodule.starProjection_unit_singleton Real hv (p : E)]
    rfl
  have heq : ((fromSphere v p : Plane v) : E) + v =
      (⟪v, (p : E)⟫)⁻¹ • (p : E) := by
    nth_rw 2 [hsplit]
    simp only [fromSphere, Submodule.coe_smul, smul_add, smul_smul,
      inv_mul_cancel₀ hp.ne', one_smul]
    exact add_comm _ _
  apply Subtype.ext
  change ‖((fromSphere v p : Plane v) : E) + v‖⁻¹ •
    (((fromSphere v p : Plane v) : E) + v) = (p : E)
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp,
    norm_eq_of_mem_sphere p, mul_one, inv_inv, smul_smul,
    mul_inv_cancel₀ hp.ne', one_smul]

theorem contDiff_toSphere_coe (hv : ‖v‖ = 1) :
    ContDiff Real ∞ (fun x : Plane v => (toSphere hv x : E)) := by
  have h : ContDiff Real ∞ (fun x : Plane v => (x : E) + v) :=
    (Plane v).subtypeL.contDiff.add contDiff_const
  exact ((h.norm Real (add_center_ne_zero hv)).inv
    (fun x => norm_ne_zero_iff.mpr (add_center_ne_zero hv x))).smul h

theorem continuousOn_fromSphere (v : E) :
    ContinuousOn (fromSphere v) {p | 0 < ⟪v, (p : E)⟫} := by
  unfold fromSphere
  apply ContinuousOn.fun_smul
  · exact ((innerSL Real v).continuous.comp continuous_subtype_val).continuousOn.inv₀
      (fun _ hp => ne_of_gt hp)
  · exact ((Plane v).orthogonalProjectionOnto.continuous.comp
      continuous_subtype_val).continuousOn

def chart (hv : ‖v‖ = 1) : OpenPartialHomeomorph (Plane v) (sphere (0 : E) 1) where
  toFun := toSphere hv
  invFun := fromSphere v
  source := univ
  target := {p | 0 < ⟪v, (p : E)⟫}
  map_source' x _ := toSphere_mem_hemisphere hv x
  map_target' _ _ := mem_univ _
  left_inv' x _ := fromSphere_toSphere hv x
  right_inv' p hp := toSphere_fromSphere hv p hp
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const
    ((innerSL Real v).continuous.comp continuous_subtype_val)
  continuousOn_toFun :=
    (continuous_induced_rng.mpr (contDiff_toSphere_coe hv).continuous).continuousOn
  continuousOn_invFun := continuousOn_fromSphere v

@[simp] theorem chart_source (hv : ‖v‖ = 1) : (chart hv).source = univ := rfl

@[simp] theorem chart_target (hv : ‖v‖ = 1) :
    (chart hv).target = {p : sphere (0 : E) 1 | 0 < ⟪v, (p : E)⟫} := rfl

@[simp] theorem chart_apply (hv : ‖v‖ = 1) (x : Plane v) :
    (chart hv x : E) = ‖(x : E) + v‖⁻¹ • ((x : E) + v) := rfl

@[simp] theorem chart_symm_apply (hv : ‖v‖ = 1) (p : sphere (0 : E) 1) :
    (chart hv).symm p = (⟪v, (p : E)⟫)⁻¹ •
      (Plane v).orthogonalProjectionOnto (p : E) := rfl

@[simp] theorem chart_zero (hv : ‖v‖ = 1) :
    (chart hv 0 : E) = v := by
  simp [chart, toSphere, hv]

theorem normalized_linear_chart (hv : ‖v‖ = 1)
    (A : E ≃L[Real] E) (B : Plane v ≃L[Real] Plane v)
    (hAv : A v = v) (hAB : ∀ x : Plane v, A (x : E) = (B x : E)) (x : Plane v) :
    ‖A (chart hv x : E)‖⁻¹ • A (chart hv x : E) = (chart hv (B x) : E) := by
  have he : A (chart hv x : E) =
      ‖(x : E) + v‖⁻¹ • ((B x : E) + v) := by
    rw [chart_apply, map_smul, map_add, hAv, hAB]
  have hn : 0 < ‖(x : E) + v‖ := norm_pos_iff.mpr (add_center_ne_zero hv x)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  change (‖(x : E) + v‖⁻¹ * ‖(B x : E) + v‖)⁻¹ •
    (‖(x : E) + v‖⁻¹ • ((B x : E) + v)) =
    ‖(B x : E) + v‖⁻¹ • ((B x : E) + v)
  rw [mul_inv_rev, inv_inv, smul_smul, mul_assoc, mul_inv_cancel₀ hn.ne', mul_one]

section FiniteDimensional

variable [FiniteDimensional Real E]

def extendLinear (v : E) (B : Plane v ≃L[Real] Plane v) : E ≃L[Real] E :=
  let e := ((Real ∙ v).prodEquivOfIsCompl (Plane v)
    (Real ∙ v).isCompl_orthogonal).toContinuousLinearEquiv
  e.symm.trans (((ContinuousLinearEquiv.refl Real (Real ∙ v)).prodCongr B).trans e)

@[simp] theorem extendLinear_center (B : Plane v ≃L[Real] Plane v) :
    extendLinear v B v = v := by
  let w : Real ∙ v := ⟨v, Submodule.mem_span_singleton_self v⟩
  change extendLinear v B (w : E) = (w : E)
  simp [extendLinear]

@[simp] theorem extendLinear_plane (B : Plane v ≃L[Real] Plane v) (x : Plane v) :
    extendLinear v B (x : E) = (B x : E) := by
  simp [extendLinear]

end FiniteDimensional

variable {n : Nat} [Fact (Module.finrank Real E = n + 1)]

theorem contMDiff_chart (hv : ‖v‖ = 1) :
    ContMDiff 𝓘(Real, Plane v) (𝓡 n) ∞ (chart hv) :=
  (contDiff_toSphere_coe hv).contMDiff.codRestrict_sphere _

theorem contMDiffOn_chart_symm (hv : ‖v‖ = 1) :
    ContMDiffOn (𝓡 n) 𝓘(Real, Plane v) ∞ (chart hv).symm (chart hv).target := by
  have hi : ContMDiff (𝓡 n) 𝓘(Real, Real) ∞
      (fun p : sphere (0 : E) 1 => ⟪v, (p : E)⟫) :=
    (innerSL Real v).contDiff.contMDiff.comp contMDiff_coe_sphere
  have hp : ContMDiff (𝓡 n) 𝓘(Real, Plane v) ∞
      (fun p : sphere (0 : E) 1 => (Plane v).orthogonalProjectionOnto (p : E)) :=
    (Plane v).orthogonalProjectionOnto.contDiff.contMDiff.comp contMDiff_coe_sphere
  exact (hi.contMDiffOn.inv₀ (fun _ hx => ne_of_gt hx)).smul hp.contMDiffOn

end Poincare.Manifold.Schoenflies.Hemisphere
