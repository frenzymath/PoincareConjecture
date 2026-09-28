import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Interior
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.ScalarBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Monotonicity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)



theorem exists_complete_bounded_nonflat_interior_geometric_limit_of_time_cap
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hκ : 0 < κ)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ k, AncientKappaNoncollapsed (F k) κ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hbase : ∀ k t, t ≤ 0 → ((F k).connection t).scalarCurvature (p k) ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ η ∧
      ∃ G : AncientPointedGeometricConvergence C
          (fun k t => (F k).metric (t - δ)) p δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.connection t).curvatureTensorNorm x ≤ 4) ∧
        (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.connection t).NonnegativeCurvatureOperator x) ∧
        (1 : ℝ) / 2 ≤ (G.limitFlow.connection 0).scalarCurvature G.base := by
  obtain ⟨δ₀, hδ₀, hδ₀one, hbuffer⟩ := exists_base_scalar_positive_time_buffer C F p
    P hc hop L hL hbound hnormalized hbase
  let δ := min δ₀ η
  have hδ : 0 < δ := lt_min hδ₀ hη
  have hδsmall : δ ≤ δ₀ := min_le_left _ _
  have hδone : δ < 1 := hδsmall.trans_lt hδ₀one
  obtain ⟨G, hcomplete, hnorm, hoperator⟩ :=
    exists_complete_bounded_interior_geometric_limit C F p P hκ hc hop hnc L hL hbound hδ
  refine ⟨δ, hδ, hδone, min_le_right _ _, G, hcomplete, hnorm, hoperator, ?_⟩
  let Fseq (k : ℕ) := (F k).bufferedExpandingFlow δ
  have htime : ∀ a b : ℝ, b < δ → ∀ᶠ k : ℕ in atTop,
      Icc a b ⊆ (fun t : ℝ => t - δ) ⁻¹' Iic 0 := by
    intro a b hb
    exact Eventually.of_forall fun k t ht => by
      change t - δ ≤ 0
      linarith [ht.2]
  apply ge_of_tendsto
    (G.tendsto_scalarCurvature_on_finite_windows Fseq hδ htime 0 hδ G.base)
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hbuffer] with k hk
  change (1 : ℝ) / 2 ≤ ((F (G.subsequence k)).connection (0 + -δ)).scalarCurvature
    (G.embedding k G.base)
  rw [zero_add, G.base_preserving]
  exact hk (-δ) ⟨by linarith, by linarith⟩



theorem exists_complete_bounded_nonflat_interior_geometric_limit
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hκ : 0 < κ)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ k, AncientKappaNoncollapsed (F k) κ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hbase : ∀ k t, t ≤ 0 → ((F k).connection t).scalarCurvature (p k) ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : AncientPointedGeometricConvergence C
          (fun k t => (F k).metric (t - δ)) p δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.connection t).curvatureTensorNorm x ≤ 4) ∧
        (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.connection t).NonnegativeCurvatureOperator x) ∧
        (1 : ℝ) / 2 ≤ (G.limitFlow.connection 0).scalarCurvature G.base := by
  obtain ⟨δ, hδ, hδone, _, G, hG⟩ :=
    exists_complete_bounded_nonflat_interior_geometric_limit_of_time_cap C F p P hκ
      hc hop hnc L hL hbound hnormalized hbase 1 (by norm_num)
  exact ⟨δ, hδ, hδone, G, hG⟩

end PoincareConjecture.RawAncientSequence
