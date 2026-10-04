/- Adapted from Mapher `PoincareMT/Proofs/M03/FiniteFourFamilyEnergy.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.Energy.Comparison.RateFiniteAlgebra

/-!
# Finite four-family coefficient energy bound

The finite coefficient estimate used by the rate producers also applies when
the principal family is retained alongside the H/A/S difference families.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped BigOperators

namespace PoincareMT.RicciFlow.Local

theorem sum_two_mul_four_family_linear_combination_le
    {I D H A S : Type*} [Fintype I] [Fintype D] [Fintype H] [Fintype A]
    [Fintype S]
    (cD : I → D → ℝ) (cH : I → H → ℝ) (cA : I → A → ℝ)
    (cS : I → S → ℝ)
    (alpha : I → ℝ) (d : D → ℝ) (h : H → ℝ) (a : A → ℝ) (s : S → ℝ)
    {eps C : ℝ} (heps : 0 < eps)
    (hC : (∑ i, ∑ j, (cD i j) ^ 2) + (∑ i, ∑ j, (cH i j) ^ 2)
      + (∑ i, ∑ j, (cA i j) ^ 2) + (∑ i, ∑ j, (cS i j) ^ 2) ≤ C)
    (hC0 : 0 ≤ C) :
    (∑ i, 2 * alpha i * (∑ j, cD i j * d j
      + ∑ j, cH i j * h j + ∑ j, cA i j * a j
      + ∑ j, cS i j * s j)) ≤
      eps * ((∑ j, (d j) ^ 2) + (∑ j, (h j) ^ 2)
        + (∑ j, (a j) ^ 2) + (∑ j, (s j) ^ 2))
      + (C / eps) * ∑ i, (alpha i) ^ 2 := by
  let B := D ⊕ (H ⊕ (A ⊕ S))
  let x : B → ℝ := Sum.elim d (Sum.elim h (Sum.elim a s))
  let c : I → B → ℝ := fun i =>
    Sum.elim (cD i) (Sum.elim (cH i) (Sum.elim (cA i) (cS i)))
  have hc : (∑ i, ∑ q, (c i q) ^ 2) ≤ C := by
    simpa [B, c, Fintype.sum_sum_type, Finset.sum_add_distrib,
      add_assoc, add_left_comm, add_comm] using hC
  have hpacked := sum_two_mul_linear_combination_le c alpha x heps hc hC0
  simpa [B, c, x, Fintype.sum_sum_type, Finset.sum_add_distrib,
    add_assoc, add_left_comm, add_comm] using hpacked

end PoincareMT.RicciFlow.Local
