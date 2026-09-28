import Mathlib.Topology.MetricSpace.Pseudo.Basic










set_option autoImplicit false

open Set

namespace Metric




theorem totallyBounded_range_of_uniform_approximation
    {X I : Type*} [PseudoMetricSpace X] (u : I → X)
    (happrox : ∀ eps : ℝ, 0 < eps → ∃ v : I → X,
      TotallyBounded (range v) ∧ ∀ i, dist (u i) (v i) < eps) :
    TotallyBounded (range u) := by
  apply totallyBounded_iff.mpr
  intro eps heps
  obtain ⟨v, hv, herr⟩ := happrox (eps / 2) (half_pos heps)
  obtain ⟨C, hCfin, hC⟩ := totallyBounded_iff.mp hv (eps / 2) (half_pos heps)
  refine ⟨C, hCfin, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := mem_iUnion.mp (hC (mem_range_self i))
  obtain ⟨hcC, hci⟩ := mem_iUnion.mp hc
  apply mem_iUnion.mpr
  refine ⟨c, mem_iUnion.mpr ⟨hcC, ?_⟩⟩
  rw [mem_ball] at hci ⊢
  calc
    dist (u i) c ≤ dist (u i) (v i) + dist (v i) c := dist_triangle _ _ _
    _ < eps / 2 + eps / 2 := add_lt_add (herr i) hci
    _ = eps := add_halves eps

end Metric
