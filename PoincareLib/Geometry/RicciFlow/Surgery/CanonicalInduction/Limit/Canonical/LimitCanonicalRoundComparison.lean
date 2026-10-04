import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalRoundUniformEnergy
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Canonical.LimitCanonicalRoundError

/-!
# Preserve the original strict round comparison witness

The actual full tensor error tends uniformly to zero on the compact
reference manifold. The old single strict witness therefore preserves
the literal accuracy and derivative order through the selected M30 maps.
MT Definitions 2.16 and 9.76, Proposition 17.1, pp. 407-408;
limit-canonical-round-jet-transfer.md, D.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X]
  [IsManifold (𝓡 3) ∞ X] [CompactSpace X]
  {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

private local instance (G : GeneralizedBlowupConvergence V J) :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance (G : GeneralizedBlowupConvergence V J) :
    ChartedSpace E3 G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance (G : GeneralizedBlowupConvergence V J) :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

/-- Actual compact convergence and the old strict round witness give
one new strict witness before every late source index and every model
point. The reference metric and connection remain fixed. MT Proposition
17.1, pp. 407-408. -/
theorem limitCanonical_round_comparison_bound
    (P : M47Predecessors.{u}) (G : GeneralizedBlowupConvergence V J)
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    (gR : RiemannianMetric 3 X) (DR : LeviCivitaData gR)
    {i : X → G.limit.sliceCarrier.carrier} (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (c : ℝ) (m : ℕ) {epsilon : ℝ}
    (hold : ∃ b : ℝ, b < epsilon ^ 2 ∧ ∀ x : X,
      singularMetricJetErrorSquared gR DR
        (fun y v => c * (G.limit.flow.metric 0).inner (i y)
          (mfderiv (𝓡 3) (𝓡 3) i y (v 0)) (mfderiv (𝓡 3) (𝓡 3) i y (v 1))) m x ≤ b) :
    ∃ bound : ℝ, bound < epsilon ^ 2 ∧ ∀ᶠ k in atTop, ∀ x : X,
      singularMetricJetErrorSquared gR DR
        (limitCanonicalRoundSourceTensor (G.embedding k) i 0
          ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩ c) m x ≤ bound := by
  let C : CovariantTensorEvaluation 3 X 2 :=
    fun y v => c * (G.limit.flow.metric 0).inner (i y)
      (mfderiv (𝓡 3) (𝓡 3) i y (v 0)) (mfderiv (𝓡 3) (𝓡 3) i y (v 1))
  have hC : IsSmoothCovariantTensor C :=
    (M44.isSmoothCovariantTensor_metric_pullback (G.limit.flow.metric 0) hi).const_mul c
  obtain ⟨b, hb, hbound⟩ := hold
  obtain ⟨eta, bound, heta, hstrict, hmargin⟩ :=
    limitCanonical_exists_strict_comparison_margin gR DR C hC m univ hb
      (fun x _ => hbound x)
  refine ⟨bound, hstrict, ?_⟩
  filter_upwards [limitCanonical_round_uniform_energy_bound P G hcompact gR DR hi c m heta,
    limitCanonical_eventually_exhaustion_univ G hcompact] with k hk hfull
  have hzero : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have hB := limitCanonical_round_source_tensor_smooth (G.embedding k) hfull hi 0 hzero c
  exact fun x => hmargin _ hB (fun y _ => hk y) x (mem_univ x)

end PoincareMT.M47
