import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Limit

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

theorem exists_buffered_limit_scalar_error_constant
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hbase : ∀ k t, t ≤ 0 → ((F k).connection t).scalarCurvature (p k) ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ {δ : ℝ}, 0 < δ →
      ∀ G : AncientPointedGeometricConvergence C (fun k t => (F k).metric (t - δ)) p δ,
        1 - (G.limitFlow.connection 0).scalarCurvature G.base ≤ B * δ ∧
        (G.limitFlow.connection 0).scalarCurvature G.base ≤ 1 := by
  obtain ⟨B, hB, herror⟩ := exists_eventually_base_scalar_time_error_constant C F p
    P hc hop L hL hbound hnormalized hbase
  refine ⟨B, hB, ?_⟩
  intro δ hδ G
  let Fseq (k : ℕ) := (F k).bufferedExpandingFlow δ
  have htime : ∀ a b : ℝ, b < δ → ∀ᶠ k : ℕ in atTop,
      Icc a b ⊆ (fun t : ℝ => t - δ) ⁻¹' Iic 0 := by
    intro a b hb
    exact Eventually.of_forall fun k t ht => by
      change t - δ ≤ 0
      linarith [ht.2]
  have hconv := G.tendsto_scalarCurvature_on_finite_windows Fseq hδ htime 0 hδ G.base
  constructor
  · apply le_of_tendsto (tendsto_const_nhds.sub hconv)
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually herror] with k hk
    change 1 - ((F (G.subsequence k)).connection (0 + -δ)).scalarCurvature
      (G.embedding k G.base) ≤ B * δ
    rw [zero_add, G.base_preserving]
    simpa only [zero_sub, neg_neg] using hk (-δ) (by linarith)
  · apply le_of_tendsto hconv
    exact Eventually.of_forall fun k => by
      change ((F (G.subsequence k)).connection (0 + -δ)).scalarCurvature
        (G.embedding k G.base) ≤ 1
      rw [zero_add, G.base_preserving]
      exact hbase (G.subsequence k) (-δ) (by linarith)

end PoincareConjecture.RawAncientSequence
