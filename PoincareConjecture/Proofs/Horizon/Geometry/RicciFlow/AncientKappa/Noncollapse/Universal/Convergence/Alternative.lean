import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ModelGeometry.NoncompactVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ModelGeometry.NoncompactCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.CompactLimit










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]




theorem M22UniversalNoncollapsingPredecessors.exists_normalized_nonround_limit
    {d : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
    (K : AncientKappaSolution 3 M) (hnonround : ¬ IsRoundAncientKappaSolution K)
    (S : AncientRescalingSequence K) :
    ∃ L : AncientAsymptoticSolitonLimitData S,
      ENNReal.ofReal universalNoncollapseModelVolume ≤
        (L.convergence.limit.flow.metric (-1)).volumeMeasure
          ((L.convergence.limit.flow.metric (-1)).ball L.convergence.limit.base (1 / 4)) ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        (L.convergence.limit.flow.connection (-1)).scalarCurvature x = 1 := by
  classical
  obtain ⟨L, hL⟩ := H.classified_limit M K S
  let C := L.convergence.limit.carrier
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  let : Nonempty C.carrier := ⟨Classical.choose C.connected.nonempty⟩
  let : ConnectedSpace C.carrier := ⟨inferInstance⟩
  obtain ⟨S₀, G, _, hflow, ⟨model⟩⟩ := hL.classified_flow
  have hscalar (x : C.carrier) : (G.flow.connection (-1)).scalarCurvature x =
      (L.convergence.limit.flow.connection (-1)).scalarCurvature x :=
    congrArg (fun F : RicciFlow 3 C.carrier (Set.Iio 0) =>
      (F.connection (-1)).scalarCurvature x) hflow
  cases model with
  | compactRound c =>
    exfalso
    apply hnonround
    apply AncientKappaRoundness.isRoundAncientKappaSolution_of_compact_round_limit
      H K S L.convergence c.compact
    exact (congrArg (fun F : RicciFlow 3 C.carrier (Set.Iio 0) =>
      ConstantPositiveSectionalCurvature (F.metric (-1)) (F.connection (-1))) hflow).mp
        (c.round_at_time (-1) (by norm_num))
  | sphereLine c =>
    refine ⟨L, ?_, ?_⟩
    · simpa only [hflow] using (c.normalized_ball_volume L.convergence.limit.base).ge
    · intro x
      exact (hscalar x).symm.trans (by
        simpa only [neg_div_neg_eq, div_one] using c.scalarCurvature (-1) (by norm_num) x)
  | quotientSphereLine q =>
    refine ⟨L, ?_, ?_⟩
    · simpa only [hflow] using q.normalized_ball_volume_lower L.convergence.limit.base
    · intro x
      exact (hscalar x).symm.trans (by
        simpa only [neg_div_neg_eq, div_one] using q.scalarCurvature (-1) (by norm_num) x)

end PoincareConjecture
