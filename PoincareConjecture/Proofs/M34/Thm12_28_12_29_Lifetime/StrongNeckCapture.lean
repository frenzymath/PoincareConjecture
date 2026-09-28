import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckRestriction
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.LimitMetricJets











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem isCompact_coordinate_map_closedStrip {r : ℝ} (hr : r < N.epsilon⁻¹) :
    IsCompact (N.coordinate_map '' (univ ×ˢ Icc (-r) r)) := by
  have hsub : (univ : Set UnitTwoSphere) ×ˢ Icc (-r) r ⊆
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro z hz
    exact ⟨hz.1, (neg_lt_neg hr).trans_le hz.2.1, hz.2.2.trans_lt hr⟩
  exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (N.coordinate_map_smooth.continuousOn.mono hsub)



theorem restrictedCarrier_subset_coordinate_map_closedStrip (epsilon : ℝ) :
    N.restrictedCarrier epsilon ⊆
      N.coordinate_map '' (univ ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹) := by
  intro x hx
  refine ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.2.1.le, hx.2.2.2.le⟩, ?_⟩
  have h := congrArg (fun y : N.carrier => (y : M))
    (N.coordinate_inverse_right x hx.1)
  rw [N.coordinate_map_eq] at h
  exact h

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.GeneralizedBlowupConvergence

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)




theorem eventually_captures_closed_neck
    (g : RiemannianMetric 3 C.limit.sliceCarrier.carrier) (N : EpsilonNeck g)
    {r : ℝ} (hr : r < N.epsilon⁻¹) (hJ : Icc (-1 : ℝ) 0 ⊆ J) :
    ∀ᶠ k : ℕ in atTop,
      N.coordinate_map '' (univ ×ˢ Icc (-r) r) ⊆ C.exhaustion.space k ∧
      Icc (-1 : ℝ) 0 ⊆ Icc (-C.exhaustion.time k) 0 := by
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset
    (N.isCompact_coordinate_map_closedStrip hr)
  filter_upwards [eventually_ge_atTop j, C.exhaustion.time_cofinal _ isCompact_Icc hJ]
    with k hk ht
  exact ⟨hj.trans (C.exhaustion.space_increasing hk), ht⟩



theorem eventually_captures_restricted_neck
    (g : RiemannianMetric 3 C.limit.sliceCarrier.carrier) (N : EpsilonNeck g)
    {epsilon : ℝ} (hepsilon : N.epsilon < epsilon) (hJ : Icc (-1 : ℝ) 0 ⊆ J) :
    ∀ᶠ k : ℕ in atTop,
      N.restrictedCarrier epsilon ⊆ C.exhaustion.space k ∧
      Icc (-1 : ℝ) 0 ⊆ Icc (-C.exhaustion.time k) 0 := by
  have hinv : epsilon⁻¹ < N.epsilon⁻¹ := inv_strictAnti₀ N.epsilon_pos hepsilon
  filter_upwards [C.eventually_captures_closed_neck g N hinv hJ] with k hk
  exact ⟨(N.restrictedCarrier_subset_coordinate_map_closedStrip epsilon).trans hk.1, hk.2⟩

end PoincareConjecture.GeneralizedBlowupConvergence
