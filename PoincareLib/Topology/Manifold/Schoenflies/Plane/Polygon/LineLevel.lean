import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Convex.Segment

/-!
# Intersecting an affine line with a height level

Geometric auxiliaries for Cairns (1951), Lemma 2.1, p. 861, and polygonal
crossing parity. A real linear height determines a unique point on a
nonhorizontal affine line at every prescribed height. Segment membership
is expressed by an unordered interval, covering either edge orientation.
See `smale/derivations/2026-09-21-line-level.md` for the source review.
-/

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Poincare.Manifold.Schoenflies.Plane

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The affine-line point at a specified height; auxiliary to Cairns, Lemma 2.1, p. 861. -/
noncomputable def lineLevelPoint (H : E →ₗ[ℝ] ℝ) (a b : E) (y : ℝ) : E :=
  AffineMap.lineMap a b ((y - H a) / (H b - H a))

/-- A nonhorizontal line meets the prescribed height; auxiliary to Cairns, 2.1, p. 861. -/
theorem linearMap_lineLevelPoint (H : E →ₗ[ℝ] ℝ) {a b : E} (hab : H a ≠ H b) (y : ℝ) :
    H (lineLevelPoint H a b y) = y := by
  simp only [lineLevelPoint, AffineMap.lineMap_apply_module', map_add, map_smul,
    map_sub, smul_eq_mul]
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.symm), sub_add_cancel]

/-- The height recovers every affine-line parameter; auxiliary to Cairns, 2.1, p. 861. -/
theorem lineLevelPoint_linearMap_lineMap (H : E →ₗ[ℝ] ℝ) {a b : E}
    (hab : H a ≠ H b) (t : ℝ) :
    lineLevelPoint H a b (H (AffineMap.lineMap a b t)) = AffineMap.lineMap a b t := by
  apply congrArg (fun s : ℝ => AffineMap.lineMap a b s)
  simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub,
    smul_eq_mul, add_sub_cancel_right]
  exact mul_div_cancel_right₀ t (sub_ne_zero.mpr hab.symm)

/-- The initial height returns the initial point even on a horizontal line;
auxiliary to Cairns, Lemma 2.1, p. 861. -/
theorem lineLevelPoint_left (H : E →ₗ[ℝ] ℝ) (a b : E) :
    lineLevelPoint H a b (H a) = a := by
  simp [lineLevelPoint]

/-- The terminal height returns the terminal point on a nonhorizontal line;
auxiliary to Cairns, Lemma 2.1, p. 861. -/
theorem lineLevelPoint_right (H : E →ₗ[ℝ] ℝ) {a b : E} (hab : H a ≠ H b) :
    lineLevelPoint H a b (H b) = b := by
  simp [lineLevelPoint, sub_ne_zero.mpr hab.symm]

/-- Every segment point is recovered from its height; auxiliary to Cairns, 2.1, p. 861. -/
theorem lineLevelPoint_eq_of_mem_segment (H : E →ₗ[ℝ] ℝ) {a b x : E}
    (hab : H a ≠ H b) (hx : x ∈ segment ℝ a b) : lineLevelPoint H a b (H x) = x := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, _, rfl⟩ := hx
  exact lineLevelPoint_linearMap_lineMap H hab t

/-- A line-level point is on the edge exactly between its endpoint heights;
auxiliary to Cairns, Lemma 2.1, p. 861. -/
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

/-- Distinct heights give distinct points of a nonhorizontal line;
auxiliary to Cairns, Lemma 2.1, p. 861. -/
theorem lineLevelPoint_injective (H : E →ₗ[ℝ] ℝ) {a b : E} (hab : H a ≠ H b) :
    Function.Injective (lineLevelPoint H a b) := by
  intro y z hyz
  have h := congrArg H hyz
  simpa only [linearMap_lineLevelPoint H hab] using h

end Module

/-- Dependence on the level is smooth, including the constant horizontal case;
auxiliary to Cairns, Lemma 2.1, p. 861. -/
theorem contDiff_lineLevelPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →ₗ[ℝ] ℝ) (a b : E) : ContDiff ℝ ∞ (lineLevelPoint H a b) := by
  exact (AffineMap.contDiff_lineMap a b).comp
    ((contDiff_id.sub contDiff_const).div_const (H b - H a))

end Poincare.Manifold.Schoenflies.Plane
