import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.ScalarBounds.NoncompactScalarAnchor
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.ScalarBounds.CompactTimeScalarBound
import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage
import PoincareLib.Geometry.Riemannian.Distance.CompleteBalls

local notation "GeneralizedBoundedDistanceHypotheses" =>
  PoincareMT.DenseGeneralizedBoundedDistanceHypotheses

/-!
# Scalar bounds on compact terminal balls

Morgan--Tian Corollary 11.16, p. 277, combines the noncompact anchor from
Claims 11.14--11.15, pp. 275--277, with compact scalar comparison. The
actual terminal metric supplies one compact connected set containing
both the requested ball and the fixed anchor, before any earlier time.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.measurableSpace FlowCarrier.borelSpace FlowCarrier.secondCountable

/-- Each compact terminal ball has one scalar bound for every included
earlier time, including zero (Morgan--Tian Corollary 11.16, p. 277). -/
theorem exists_finite_limit_compact_scalar_bound_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ),
        0 < epsilon → epsilon ≤ epsilon0 → 0 < C →
        GeneralizedBoundedDistanceHypotheses S epsilon C →
      ∀ (T : ℝ), 0 < T →
      ∀ G : GeneralizedBlowupConvergence S (Ioc (-T) 0),
      ∀ A : ℝ, 0 < A →
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ t, t ∈ Ioc (-T) 0 →
          ∀ x, x ∈ closure ((G.limit.flow.metric 0).ball G.limit.base A) →
            (G.limit.flow.connection t).scalarCurvature x ≤ B := by
  obtain ⟨epsilonAnchor, hAnchorPos, hAnchorMax, hAnchor⟩ :=
    exists_noncompact_limit_scalar_anchor_threshold P
  obtain ⟨epsilonComparison, hComparisonPos, _hComparisonMax, hComparison⟩ :=
    exists_compact_scalar_bound_of_anchors_threshold P
  obtain ⟨epsilonCompact, hCompactPos, _hCompactMax, hCompact⟩ :=
    exists_compact_limit_uniform_scalar_bound_threshold P
  refine ⟨min epsilonAnchor (min epsilonComparison epsilonCompact),
    lt_min hAnchorPos (lt_min hComparisonPos hCompactPos),
    (min_le_left _ _).trans hAnchorMax, ?_⟩
  intro S epsilon C hepsilon hepsilonLe hC H T hT G A hA
  have heAnchor : epsilon ≤ epsilonAnchor := hepsilonLe.trans (min_le_left _ _)
  have heComparison : epsilon ≤ epsilonComparison :=
    hepsilonLe.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heCompact : epsilon ≤ epsilonCompact :=
    hepsilonLe.trans ((min_le_right _ _).trans (min_le_right _ _))
  by_cases hcompact : IsCompact (univ : Set G.limit.carrier.carrier)
  · obtain ⟨B, hB, hbound⟩ := hCompact S epsilon C hepsilon heCompact hC H T hT G hcompact
    exact ⟨B, hB, fun t ht x _hx => hbound t ht x⟩
  · obtain ⟨y, Bmin, _hBmin, hAnchorBound⟩ :=
      hAnchor S epsilon C hepsilon heAnchor hC H T hT G hcompact
    let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
    let g := G.limit.flow.metric 0
    let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
    let rho := max A ((g.edist G.limit.base y).toReal + 1)
    have hrho : 0 < rho := hA.trans_le (le_max_left _ _)
    let X := closure (g.ball G.limit.base rho)
    have hXcompact : IsCompact X := by
      apply IsCompact.of_isClosed_subset
        (g.isCompact_closedBall_of_metricComplete
          (G.limit.complete 0 G.limit.zero_mem) G.limit.base rho) isClosed_closure
      apply closure_minimal
        (fun x (hx : g.edist G.limit.base x < ENNReal.ofReal rho) => hx.le)
      exact isClosed_le (continuous_const.edist continuous_id) continuous_const
    have hpball : G.limit.base ∈ g.ball G.limit.base rho := by
      change g.edist G.limit.base G.limit.base < ENNReal.ofReal rho
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
        ENNReal.ofReal_pos.mpr hrho
    have hXconnected : IsConnected X :=
      ⟨⟨G.limit.base, subset_closure hpball⟩,
        (g.isPreconnected_ball G.limit.base rho).closure⟩
    have hyX : y ∈ X := by
      apply subset_closure
      change g.edist G.limit.base y < ENNReal.ofReal rho
      apply (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top G.limit.base y)).mpr
      exact (lt_add_one _).trans_le (le_max_right _ _)
    obtain ⟨B, hB, hbound⟩ := hComparison S epsilon C hepsilon heComparison hC H T hT
      G X hXcompact hXconnected Bmin (fun t ht => ⟨y, hyX, hAnchorBound t ht⟩)
    have hsubset : closure (g.ball G.limit.base A) ⊆ X := by
      apply closure_mono
      intro x hx
      exact hx.trans_le (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact ⟨B, hB, fun t ht x hx => hbound t ht x (hsubset hx)⟩

end PoincareMT.M30
