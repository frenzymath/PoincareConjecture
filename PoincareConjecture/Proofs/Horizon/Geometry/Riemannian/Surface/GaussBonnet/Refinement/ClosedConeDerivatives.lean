import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace PoincareConjecture.Topology.Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_mem_closed_cone_of_eventually
    {A : Set E} (hA : IsClosed A)
    (hsmul : ∀ r : ℝ, 0 < r → ∀ v ∈ A, r • v ∈ A)
    {f : ℝ → E} {v : E} (hf : HasDerivAt f v 0)
    (hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t - f 0 ∈ A) : v ∈ A := by
  apply hA.mem_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [hnear, self_mem_nhdsWithin] with t ht hpos
  simpa only [zero_add] using hsmul t⁻¹ (inv_pos.mpr hpos) (f t - f 0) ht

theorem nonpos_of_translates_mem_reflex_quadrant {a b : ℝ}
    (h1 : ∀ s : ℝ, 0 ≤ s → a + s ≤ 0 ∨ b ≤ 0)
    (h2 : ∀ s : ℝ, 0 ≤ s → a ≤ 0 ∨ b + s ≤ 0) : a ≤ 0 ∧ b ≤ 0 := by
  constructor
  · have h := h2 (max 0 (-b) + 1) (by linarith [le_max_left 0 (-b)])
    exact h.resolve_right (by linarith [le_max_right 0 (-b)])
  · have h := h1 (max 0 (-a) + 1) (by linarith [le_max_left 0 (-a)])
    exact h.resolve_left (by linarith [le_max_right 0 (-a)])

theorem nonpos_coordinates_of_ray_translates
    (l1 l2 : E →ₗ[ℝ] ℝ) (u d1 d2 : E)
    (h11 : l1 d1 = 1) (h21 : l2 d1 = 0)
    (h12 : l1 d2 = 0) (h22 : l2 d2 = 1)
    (h1 : ∀ s : ℝ, 0 ≤ s → l1 (u + s • d1) ≤ 0 ∨ l2 (u + s • d1) ≤ 0)
    (h2 : ∀ s : ℝ, 0 ≤ s → l1 (u + s • d2) ≤ 0 ∨ l2 (u + s • d2) ≤ 0) :
    l1 u ≤ 0 ∧ l2 u ≤ 0 := by
  apply nonpos_of_translates_mem_reflex_quadrant
  · simpa only [map_add, map_smul, h11, h21, smul_eq_mul, mul_one, mul_zero,
      add_zero] using h1
  · simpa only [map_add, map_smul, h12, h22, smul_eq_mul, mul_one, mul_zero,
      add_zero] using h2

end PoincareConjecture.Topology.Surface
