import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Constants

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}
  (G : AncientCompactTimeConvergence S)

theorem eventually_model_ball_volume_lower
    (hvol : ENNReal.ofReal universalNoncollapseModelVolume ≤
      (G.limit.flow.metric (-1)).volumeMeasure
        ((G.limit.flow.metric (-1)).ball G.limit.base (1 / 4))) :
    ∀ᶠ k in atTop, ENNReal.ofReal universalNoncollapseVolume ≤
      ((S.rescaling (G.subsequence k)).flow.metric (-1)).volumeMeasure
        (((S.rescaling (G.subsequence k)).flow.metric (-1)).ball
          (S.base (G.subsequence k)) (1 / 2)) := by
  filter_upwards [G.eventually_ball_volume_bounds (t := -1) (r := 1 / 2)
    (C := 2) (by norm_num) G.limit.base (by norm_num) (by norm_num)] with k hk
  have hbase : ((G.embedding k).toFun (-1, G.limit.base)).2 = S.base (G.subsequence k) :=
    congrArg Prod.snd (G.base_preserving k)
  have h := hk.2
  rw [hbase] at h
  norm_num at h
  have hv := ENNReal.div_le_of_le_mul' (hvol.trans h)
  simpa [universalNoncollapseVolume, ENNReal.ofReal_div_of_pos] using hv

end PoincareConjecture.AncientCompactTimeConvergence
