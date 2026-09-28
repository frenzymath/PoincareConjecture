import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFrontierHeight
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem exists_oriented_forward_transfer_accuracy :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        P.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        P.center ∉ N.carrier →
          ∃ Q : EpsilonNeck g, (Q = P ∨ Q = P.reversed) ∧
            N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ Q.carrier ∧
            N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
              Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2) := by
  obtain ⟨ε₁, hε₁, _, hbounds⟩ := exists_frontier_transition_height_bounds_m28.{u}
  obtain ⟨ε₂, hε₂, _, hcontain⟩ :=
    exists_closure_positive_quarter_subset_of_central_sphere_contact_m28.{u}
  refine ⟨min ε₁ (min ε₂ (1 / 10000)),
    lt_min hε₁ (lt_min hε₂ (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq hx hout
  have hε' : N.epsilon ≤ ε₁ := hε.trans (min_le_left _ _)
  have hfront : P.center ∈ frontier N.carrier := by
    rw [N.carrier_open.frontier_eq]
    exact ⟨closure_mono (N.region_subset_carrier _ _) hx, hout⟩
  obtain ⟨σ, hσ, hheight⟩ := hbounds N P hε' heq P.center hfront hx
    P.center_on_central_sphere
  have hpositive := hcontain N P
    (hε.trans ((min_le_right _ _).trans (min_le_left _ _))) heq
    ⟨P.center, hx, P.center_on_central_sphere⟩
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hAlarge : (10000 : ℝ) ≤ N.epsilon⁻¹ := by
    have hsmall : N.epsilon ≤ (1 / 10000 : ℝ) :=
      hε.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h := mul_le_mul_of_nonneg_right hsmall (le_of_lt hA)
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  rcases hσ with rfl | rfl
  · refine ⟨P, Or.inl rfl, ?_, ?_⟩
    · intro y hy
      exact hpositive (subset_closure hy)
    · intro y hy
      have hz := N.coordinate_inverse_mem y hy.1
      have ha : (N.coordinate_inverse y).2 ∈
          Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := hy.2
      have hh := hheight (N.coordinate_inverse y).1
        (N.coordinate_inverse y).2 ha
      have hmap : N.coordinate_map
          ((N.coordinate_inverse y).1, (N.coordinate_inverse y).2) = y :=
        N.coordinate_map_coordinate_inverse hy.1
      rw [hmap] at hh
      have hlow : -N.epsilon⁻¹ < (P.coordinate_inverse y).2 := by
        nlinarith [hh.1, Real.pi_le_four, ha.1, ha.2]
      have hupp : (P.coordinate_inverse y).2 < N.epsilon⁻¹ / 2 := by
        nlinarith [hh.2, Real.pi_le_four, ha.1, ha.2]
      exact ⟨hpositive (subset_closure hy), hlow, hupp⟩
  · refine ⟨P.reversed, Or.inr rfl, ?_, ?_⟩
    · intro y hy
      simpa only [reversed_carrier] using hpositive (subset_closure hy)
    · intro y hy
      have hz := N.coordinate_inverse_mem y hy.1
      have ha : (N.coordinate_inverse y).2 ∈
          Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := hy.2
      have hh := hheight (N.coordinate_inverse y).1
        (N.coordinate_inverse y).2 ha
      have hmap : N.coordinate_map
          ((N.coordinate_inverse y).1, (N.coordinate_inverse y).2) = y :=
        N.coordinate_map_coordinate_inverse hy.1
      rw [hmap] at hh
      have hhlow : -1.1 * (N.epsilon⁻¹ - (N.coordinate_inverse y).2) -
          5 * Real.pi ≤ -(P.coordinate_inverse y).2 := by
        simpa only [one_mul, neg_one_mul] using hh.1
      have hhupper : -(P.coordinate_inverse y).2 ≤
          -0.9 * (N.epsilon⁻¹ - (N.coordinate_inverse y).2) + 5 * Real.pi := by
        simpa only [one_mul, neg_one_mul] using hh.2
      have hlow : -N.epsilon⁻¹ <
          (P.reversed.coordinate_inverse y).2 := by
        have hlow' : -N.epsilon⁻¹ < -(P.coordinate_inverse y).2 := by
          nlinarith [hhlow, Real.pi_le_four, ha.1, ha.2]
        simpa only [reversed_coordinate_inverse] using hlow'
      have hupp : (P.reversed.coordinate_inverse y).2 <
          N.epsilon⁻¹ / 2 := by
        have hupp' : -(P.coordinate_inverse y).2 < N.epsilon⁻¹ / 2 := by
          nlinarith [hhupper, Real.pi_le_four, ha.1, ha.2]
        simpa only [reversed_coordinate_inverse] using hupp'
      exact ⟨hpositive (subset_closure hy), hlow, hupp⟩

end PoincareConjecture.EpsilonNeck
