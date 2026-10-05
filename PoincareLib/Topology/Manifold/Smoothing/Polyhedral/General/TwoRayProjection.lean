import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.TangentCylinderSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Normalized scalar projections of a two-ray star

A projection fixing the first endpoint embeds two independent source
segments precisely when the second endpoint has negative image.
See Cairns 1940, Section 11, p. 807, and M76 derivation 39.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The one-dimensional full star with its two outer endpoints.
See Cairns pp. 800, 807 and M76 derivation 39. -/
def twoRayStar (u v : E) : Set E := segment ℝ 0 u ∪ segment ℝ 0 v

private theorem segment_zero_eq_image (u : E) :
    segment ℝ 0 u = (fun a : ℝ => a • u) '' Icc (0 : ℝ) 1 := by
  simpa only [smul_zero, zero_add] using segment_eq_image ℝ (0 : E) u

/-- Fixing the first endpoint forces the other endpoint to lie
strictly on the opposite side of zero for a scalar projection to
embed the entire independent two-ray star.
See Cairns p. 807 and M76 derivation 39. -/
theorem injOn_twoRayStar_iff (u v : E) (hv : LinearIndependent ℝ ![u, v])
    (Q : E →L[ℝ] ℝ) (hu : Q u = 1) : InjOn Q (twoRayStar u v) ↔ Q v < 0 := by
  constructor
  · intro h
    by_contra hn
    have hq : 0 ≤ Q v := le_of_not_gt hn
    have hd : 0 < 1 + Q v := by linarith
    let a : ℝ := Q v / (1 + Q v)
    let b : ℝ := 1 / (1 + Q v)
    have ha : a ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hq hd.le, (div_le_one hd).mpr (by linarith)⟩
    have hb : b ∈ Icc (0 : ℝ) 1 :=
      ⟨(div_pos one_pos hd).le, (div_le_one hd).mpr (by linarith)⟩
    have he : a • u = b • v := h
      (Or.inl (segment_zero_eq_image u ▸ mem_image_of_mem _ ha))
      (Or.inr (segment_zero_eq_image v ▸ mem_image_of_mem _ hb)) (by
        rw [map_smul, map_smul, hu]
        change a * 1 = b * Q v
        dsimp only [a, b]
        ring)
    have hbzero := (hv.eq_zero_of_pair' he).2
    exact (div_pos one_pos hd).ne' hbzero
  · intro hvneg x hx y hy he
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [segment_zero_eq_image] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      have hab : a = b := by simpa only [map_smul, hu, smul_eq_mul, mul_one] using he
      rw [hab]
    · rw [segment_zero_eq_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have he' : a = b * Q v := by simpa only [map_smul, hu, smul_eq_mul, mul_one] using he
      have hb0 : b = 0 := by nlinarith [ha.1, hb.1]
      have ha0 : a = 0 := by simpa only [hb0, zero_mul] using he'
      simp only [ha0, hb0, zero_smul]
    · rw [segment_zero_eq_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have he' : a * Q v = b := by simpa only [map_smul, hu, smul_eq_mul, mul_one] using he
      have ha0 : a = 0 := by nlinarith [ha.1, hb.1]
      have hb0 : b = 0 := by simpa only [ha0, zero_mul] using he'.symm
      simp only [ha0, hb0, zero_smul]
    · rw [segment_zero_eq_image] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      have he' : a * Q v = b * Q v := by simpa only [map_smul, smul_eq_mul] using he
      rw [mul_right_cancel₀ hvneg.ne he']

end Geometry
