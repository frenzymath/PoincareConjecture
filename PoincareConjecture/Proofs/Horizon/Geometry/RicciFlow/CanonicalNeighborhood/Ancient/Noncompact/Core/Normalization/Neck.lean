import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Normalization.Carrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Rescaling









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

section Carrier

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}



def EpsilonNeck.mapIsometry (A : EpsilonNeck g)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (he : MetricHomothety g h e 1)
    (D : LeviCivitaData h) : EpsilonNeck h :=
  A.m48_pullback (MetricHomothety.symm_one e he)
    (Homothety.metricHomothetyCalculus h g e.symm 1 zero_lt_one
      (MetricHomothety.symm_one e he)) D

@[simp] theorem EpsilonNeck.mapIsometry_epsilon (A : EpsilonNeck g)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (he : MetricHomothety g h e 1)
    (D : LeviCivitaData h) : (A.mapIsometry e he D).epsilon = A.epsilon := rfl

@[simp] theorem EpsilonNeck.mapIsometry_scale (A : EpsilonNeck g)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (he : MetricHomothety g h e 1)
    (D : LeviCivitaData h) : (A.mapIsometry e he D).scale = A.scale := rfl

@[simp] theorem EpsilonNeck.mapIsometry_center (A : EpsilonNeck g)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (he : MetricHomothety g h e 1)
    (D : LeviCivitaData h) : (A.mapIsometry e he D).center = e A.center := rfl

end Carrier

namespace AncientKappaNormalization

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {q : M}



theorem metric_zero_eq_rescaled (A : AncientKappaNormalization K q 0) :
    A.target.flow.metric 0 = rescaledMetric (K.flow.metric 0) A.scale A.scale_pos := by
  have hi : (A.target.flow.metric 0).inner =
      (rescaledMetric (K.flow.metric 0) A.scale A.scale_pos).inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simpa only [zero_div, zero_add, rescaledMetric_inner] using A.metric_eq 0 x v w
  generalize A.target.flow.metric 0 = g at hi ⊢
  generalize rescaledMetric (K.flow.metric 0) A.scale A.scale_pos = h at hi ⊢
  cases g
  cases h
  cases hi
  rfl



theorem exists_epsilonNeck (A : AncientKappaNormalization K q 0)
    (N : EpsilonNeck (K.flow.metric 0)) :
    ∃ N' : EpsilonNeck (A.target.flow.metric 0),
      N'.epsilon = N.epsilon ∧ N'.scale = Real.sqrt A.scale * N.scale ∧
        N'.center = N.center := by
  obtain ⟨N', heps, hscale, hcenter, _, _, _, _⟩ :=
    EpsilonNeck.exists_of_metric_eq A.metric_zero_eq_rescaled.symm
      (N.rescale A.scale A.scale_pos)
  exact ⟨N', heps, hscale, hcenter⟩

end AncientKappaNormalization

namespace AncientKappaSolution

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  (K : AncientKappaSolution 3 M) (q : M) {kappa : ℝ}
  (hkappa : 0 < kappa) (hnoncollapsed : AncientKappaNoncollapsed K.flow kappa)
  (hnormalized : (K.flow.connection 0).scalarCurvature q = 1)


def epsilonNeckToSmallBased (N : EpsilonNeck (K.flow.metric 0)) :
    EpsilonNeck ((K.toSmallBased q hkappa hnoncollapsed hnormalized).flow.flow.metric 0) :=
  N.mapIsometry (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M)
    (K.flow.metricHomothety_shrink 0) (K.flow.shrink.connection 0)

@[simp] theorem epsilonNeckToSmallBased_epsilon (N : EpsilonNeck (K.flow.metric 0)) :
    (K.epsilonNeckToSmallBased q hkappa hnoncollapsed hnormalized N).epsilon = N.epsilon := rfl

@[simp] theorem epsilonNeckToSmallBased_scale (N : EpsilonNeck (K.flow.metric 0)) :
    (K.epsilonNeckToSmallBased q hkappa hnoncollapsed hnormalized N).scale = N.scale := rfl

@[simp] theorem epsilonNeckToSmallBased_center (N : EpsilonNeck (K.flow.metric 0)) :
    (K.epsilonNeckToSmallBased q hkappa hnoncollapsed hnormalized N).center =
      equivShrink M N.center := rfl

end AncientKappaSolution

end PoincareConjecture
