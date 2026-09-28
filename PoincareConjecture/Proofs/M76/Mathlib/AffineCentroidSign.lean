import PoincareConjecture.Proofs.M76.Mathlib.CentroidMesh









set_option autoImplicit false

open Set
open scoped BigOperators

namespace Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem affine_nonpos_on_hull_of_centroid (s : Finset E) (hs : s.Nonempty)
    (A : E →ᵃ[ℝ] ℝ)
    (hside : (∀ v ∈ s, A v ≤ 0) ∨ (∀ v ∈ s, 0 ≤ A v))
    (hcent : A (s.centroid ℝ id) ≤ 0) :
    ∀ x ∈ convexHull ℝ (s : Set E), A x ≤ 0 := by
  have hvertices : ∀ v ∈ s, A v ≤ 0 := by
    rcases hside with h | h
    · exact h
    · have hws := s.sum_centroidWeights_eq_one_of_nonempty ℝ hs
      have hav : A (s.centroid ℝ id) = (s.card : ℝ)⁻¹ * ∑ v ∈ s, A v := by
        rw [centroid_def, map_affineCombination _ _ _ hws,
          affineCombination_eq_linear_combination _ _ _ hws]
        simp only [centroidWeights_apply, Function.comp_apply, id_eq, smul_eq_mul, mul_sum]
      have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      have hsum : ∑ v ∈ s, A v = 0 := by
        have hle : ∑ v ∈ s, A v ≤ 0 := by
          rw [hav] at hcent
          have hle : (s.card : ℝ)⁻¹ * ∑ v ∈ s, A v ≤ (s.card : ℝ)⁻¹ * 0 := by
            simpa only [mul_zero] using hcent
          exact (mul_le_mul_iff_right₀ (inv_pos.mpr hcard)).mp hle
        exact le_antisymm hle (sum_nonneg h)
      exact fun v hv => ((sum_eq_zero_iff_of_nonneg h).mp hsum v hv).le
  exact convexHull_min hvertices ((convex_Iic (0 : ℝ)).affine_preimage A)

end Finset
