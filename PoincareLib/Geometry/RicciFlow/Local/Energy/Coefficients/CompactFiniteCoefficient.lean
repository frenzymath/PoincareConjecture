/- Adapted from Mapher `PoincareMT/Proofs/M03/CompactFiniteCoefficient.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.Energy.Comparison.RateFiniteAlgebra

set_option autoImplicit false

open scoped BigOperators

namespace PoincareMT.RicciFlow.Local

/- A finite family of continuous coefficient functions is uniformly bounded on
   a compact domain after taking the square-sum used by the rate algebra. -/
theorem exists_compact_finite_square_sum_bound
    {X I B : Type*} [TopologicalSpace X] [Fintype I] [Fintype B]
    {K : Set X} (hK : IsCompact K)
    (c : X → I → B → ℝ)
    (hc : ∀ i b, ContinuousOn (fun x => c x i b) K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, (∑ i, ∑ b, (c x i b) ^ 2) ≤ C := by
  let S : X → ℝ := fun x => ∑ i, ∑ b, (c x i b) ^ 2
  have hS : ContinuousOn S K := by
    unfold S
    apply continuousOn_finsetSum
    intro i hi
    apply continuousOn_finsetSum
    intro b hb
    exact (hc i b).pow 2
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hS
  refine ⟨max C₀ 0, le_max_right C₀ 0, ?_⟩
  intro x hx
  have hnorm : ‖S x‖ ≤ max C₀ 0 :=
    (hC₀ x hx).trans (le_max_left C₀ 0)
  exact (le_abs_self (S x)).trans hnorm

end PoincareMT.RicciFlow.Local
