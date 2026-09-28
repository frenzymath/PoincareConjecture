import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Convex.Segment

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Poincare.Manifold.Schoenflies.Plane

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def lineLevelPoint (H : E →ₗ[ℝ] ℝ) (a b : E) (y : ℝ) : E :=
  AffineMap.lineMap a b ((y - H a) / (H b - H a))

theorem linearMap_lineLevelPoint (H : E →ₗ[ℝ] ℝ) {a b : E} (hab : H a ≠ H b) (y : ℝ) :
    H (lineLevelPoint H a b y) = y := by
  simp only [lineLevelPoint, AffineMap.lineMap_apply_module', map_add, map_smul,
    map_sub, smul_eq_mul]
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.symm), sub_add_cancel]

theorem lineLevelPoint_linearMap_lineMap (H : E →ₗ[ℝ] ℝ) {a b : E}
    (hab : H a ≠ H b) (t : ℝ) :
    lineLevelPoint H a b (H (AffineMap.lineMap a b t)) = AffineMap.lineMap a b t := by
  apply congrArg (fun s : ℝ => AffineMap.lineMap a b s)
  simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub,
    smul_eq_mul, add_sub_cancel_right]
  exact mul_div_cancel_right₀ t (sub_ne_zero.mpr hab.symm)

theorem lineLevelPoint_left (H : E →ₗ[ℝ] ℝ) (a b : E) :
    lineLevelPoint H a b (H a) = a := by
  simp [lineLevelPoint]

theorem lineLevelPoint_right (H : E →ₗ[ℝ] ℝ) {a b : E} (hab : H a ≠ H b) :
    lineLevelPoint H a b (H b) = b := by
  simp [lineLevelPoint, sub_ne_zero.mpr hab.symm]

theorem lineLevelPoint_eq_of_mem_segment (H : E →ₗ[ℝ] ℝ) {a b x : E}
    (hab : H a ≠ H b) (hx : x ∈ segment ℝ a b) : lineLevelPoint H a b (H x) = x := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, _, rfl⟩ := hx
  exact lineLevelPoint_linearMap_lineMap H hab t

theorem lineLevelPoint_mem_segment_iff (H : E →ₗ[ℝ] ℝ) {a b : E}
    (hab : H a ≠ H b) (y : ℝ) :
    lineLevelPoint H a b y ∈ segment ℝ a b ↔ y ∈ uIcc (H a) (H b) := by
  have himage : H '' segment ℝ a b = uIcc (H a) (H b) := by
    simpa only [segment_eq_uIcc, LinearMap.coe_toAffineMap] using
      image_segment ℝ H.toAffineMap a b
  constructor
  · intro hx
    simpa only [himage, linearMap_lineLevelPoint H hab y] using mem_image_of_mem H hx
  · intro hy
    rw [← himage] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [lineLevelPoint_eq_of_mem_segment H hab hx]
    exact hx

theorem lineLevelPoint_injective (H : E →ₗ[ℝ] ℝ) {a b : E} (hab : H a ≠ H b) :
    Function.Injective (lineLevelPoint H a b) := by
  intro y z hyz
  have h := congrArg H hyz
  simpa only [linearMap_lineLevelPoint H hab] using h

end Module

theorem contDiff_lineLevelPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →ₗ[ℝ] ℝ) (a b : E) : ContDiff ℝ ∞ (lineLevelPoint H a b) := by
  exact (AffineMap.contDiff_lineMap a b).comp
    ((contDiff_id.sub contDiff_const).div_const (H b - H a))

end Poincare.Manifold.Schoenflies.Plane
