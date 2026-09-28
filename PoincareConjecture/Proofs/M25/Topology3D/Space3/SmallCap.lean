import Mathlib.Analysis.InnerProductSpace.Basic










set_option autoImplicit false

open Set Metric Filter
open scoped Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]




theorem exists_sphericalCap_subset (u : E) (hu : ‖u‖ = 1)
    {U : Set E} (hU : U ∈ 𝓝 u) :
    ∃ a : ℝ, a ∈ Ioo (1 / 2 : ℝ) 1 ∧ {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} ⊆ U := by
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hmax : max (1 / 2 : ℝ) (1 - eps ^ 2 / 2) < 1 := by
    apply max_lt_iff.mpr
    constructor
    · norm_num
    · nlinarith [sq_pos_of_pos heps]
  obtain ⟨a, ha, ha1⟩ := exists_between hmax
  refine ⟨a, ⟨(le_max_left _ _).trans_lt ha, ha1⟩, ?_⟩
  intro x hx
  apply hball
  rw [mem_ball, dist_eq_norm]
  have hsq : ‖x - u‖ ^ 2 = 2 - 2 * ⟪u, x⟫_ℝ := by
    rw [norm_sub_sq_real, hx.1, hu, real_inner_comm x u]
    ring
  have haeps := (le_max_right (1 / 2 : ℝ) (1 - eps ^ 2 / 2)).trans_lt ha
  nlinarith [norm_nonneg (x - u), hx.2]

end PoincareConjecture.M25.Topology3D
