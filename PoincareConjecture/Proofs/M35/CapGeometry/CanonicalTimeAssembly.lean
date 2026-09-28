import PoincareConjecture.Proofs.M35.CapGeometry.InitialCanonicalSlab
import PoincareConjecture.Proofs.M35.CapGeometry.FarTipUniformWindow
import PoincareConjecture.Proofs.M35.CapGeometry.IndependentScalarRate

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem canonical_of_bounded_tip_caps
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (epsilon : ℝ)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2)
    (hbounded : ∀ D : ℝ, 0 ≤ D → ∃ C₀ H : ℝ, 0 < C₀ ∧ 0 < H ∧
      ∀ C ≥ C₀, ∀ t, ∀ _ht : t ∈ Ico 0 E.flow.base.lifetime,
        ∀ x : StandardCapSpace, H ≤ (E.flow.connection t).scalarCurvature x →
          ((E.flow.metric t).edist 0 x).toReal *
              Real.sqrt ((E.flow.connection t).scalarCurvature x) ≤ D →
            Nonempty (StandardCapNeighborhood E.atlas E.flow t epsilon C x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace,
        StandardCanonicalAlternative E.atlas E.flow t x epsilon C := by
  obtain ⟨B, hB, hfar⟩ := OrdinaryRealization.exists_far_tip_prescribed_window_threshold
    P E epsilon he hehalf
  obtain ⟨C₀, H, hC₀, _hH, hnear⟩ := hbounded B hB.le
  obtain ⟨c, hc, hrate⟩ := E.scalar_lower_rate_from_unit_time P
  let M := max B H
  have hM : 0 < M := hB.trans_le (le_max_left _ _)
  let theta := max (1 / 2 : ℝ) (1 - c / M)
  have htheta : 0 < theta := (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (le_max_left _ _)
  have hthetaone : theta < 1 := max_lt (by norm_num)
    (sub_lt_self 1 (div_pos hc hM))
  have hthetalt : theta < E.flow.base.lifetime := E.lifetime_one.symm ▸ hthetaone
  obtain ⟨C₁, _hC₁, hinitial⟩ := initial_slab_canonical P E htheta hthetalt he hehalf
  refine ⟨max C₀ C₁, hC₀.trans_le (le_max_left _ _), ?_⟩
  intro t ht x
  by_cases htinitial : t ≤ theta
  · exact hinitial (max C₀ C₁) (le_max_right _ _) t ⟨ht.1, htinitial⟩ x
  · have htlater : theta ≤ t := (lt_of_not_ge htinitial).le
    have htone : t < 1 := E.lifetime_one ▸ ht.2
    have hden : 0 < 1 - t := sub_pos.mpr htone
    have hclock : 1 - t ≤ c / M := by
      have h := (le_max_right (1 / 2 : ℝ) (1 - c / M)).trans htlater
      linarith only [h]
    have hproduct : M * (1 - t) ≤ c := calc
      M * (1 - t) ≤ M * (c / M) := mul_le_mul_of_nonneg_left hclock hM.le
      _ = c := mul_div_cancel₀ c hM.ne'
    have hhigh : M ≤ (E.flow.connection t).scalarCurvature x :=
      ((le_div_iff₀ hden).mpr hproduct).trans (hrate t ht x)
    by_cases hdist : B ≤ ((E.flow.metric t).edist 0 x).toReal *
        Real.sqrt ((E.flow.connection t).scalarCurvature x)
    · obtain ⟨N⟩ := hfar t ht x ((le_max_left B H).trans hhigh) hdist
      exact StandardCanonicalAlternative.evolving_neck N
    · obtain ⟨N⟩ := hnear (max C₀ C₁) (le_max_left _ _) t ht x
        ((le_max_right B H).trans hhigh) (le_of_not_ge hdist)
      exact StandardCanonicalAlternative.cap N

end PoincareConjecture.M35.Uniqueness
