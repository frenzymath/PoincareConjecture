import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.UniformLimits
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.CylinderCover


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem exists_reducedLengthPullback_locallyUniform_limit
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ l : G.limit.carrier.carrier × ℝ → ℝ,
      ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)) ∧
      TendstoLocallyUniformlyOn (fun k z => G.reducedLengthPullback (σ k) z.1 z.2)
        l atTop (univ ×ˢ Ioi (0 : ℝ)) := by
  obtain ⟨b, d, hd⟩ := G.limit.carrier.exists_positive_coordinateCylinder_cover
  obtain ⟨σ, hσ, f, hf, hlim⟩ := G.exists_reducedLengthPullback_common_uniformSubsequence P
    (fun i => (d i).center) (fun i => (d i).coordinate) (fun i => (d i).radius)
    (fun i => (d i).lower) (fun i => (d i).upper) (fun i => (d i).radius_pos)
    (fun i => ((d i).time_subset ⟨le_rfl, (d i).lower_lt_upper.le⟩).1)
    (fun i => (d i).lower_lt_upper.le) (fun i => (d i).chart_subset)
  obtain ⟨l, hl, hconv⟩ :=
    G.limit.carrier.exists_continuous_locallyUniform_limit_of_positive_coordinateCylinder_limits
      b d hd (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) f hf hlim
  exact ⟨σ, hσ, l, hl, hconv⟩

end PoincareConjecture.AncientCompactTimeConvergence
