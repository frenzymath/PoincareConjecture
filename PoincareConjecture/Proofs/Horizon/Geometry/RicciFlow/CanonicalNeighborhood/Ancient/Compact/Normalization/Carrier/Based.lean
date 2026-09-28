import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Small
import PoincareConjecture.Definitions.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Shrink
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.StrongNeck

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

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
  (K : AncientKappaSolution 3 M) (p : M) {kappa : ℝ}
  (hkappa : 0 < kappa) (hnoncollapsed : AncientKappaNoncollapsed K.flow kappa)
  (hnormalized : (K.flow.connection 0).scalarCurvature p = 1)

def toSmallBased : BasedKappaSolution kappa :=
  ScalarDerivatives.smallBasedKappaSolution K p kappa hkappa hnoncollapsed hnormalized

@[simp] theorem toSmallBased_flow :
    (K.toSmallBased p hkappa hnoncollapsed hnormalized).flow.flow = K.flow.shrink := rfl

@[simp] theorem toSmallBased_base :
    (K.toSmallBased p hkappa hnoncollapsed hnormalized).base = equivShrink M p := rfl

theorem toSmallBased_isCompact (hcompact : IsCompact (univ : Set M)) :
    IsCompact (univ : Set
      (K.toSmallBased p hkappa hnoncollapsed hnormalized).carrier.carrier) := by
  simpa only [image_univ, EquivLike.range_eq_univ] using
    hcompact.image (Poincare.Topology.SecondCountable.homeomorphShrink M).continuous

theorem toSmallBased_noEmbeddedTrivialNormalProjectivePlane
    (hno : NoEmbeddedTrivialNormalProjectivePlane K) :
    NoEmbeddedTrivialNormalProjectivePlane
      (K.toSmallBased p hkappa hnoncollapsed hnormalized).flow := by
  rintro ⟨f, hf⟩
  exact hno ⟨(Poincare.Topology.SecondCountable.homeomorphShrink M).symm ∘ f,
    (Poincare.Topology.SecondCountable.homeomorphShrink M).symm.isOpenEmbedding.comp hf⟩

theorem cap_of_toSmallBased {epsilon C : ℝ}
    (hcap : ∃ A : CapCertificate
        ((K.toSmallBased p hkappa hnoncollapsed hnormalized).flow.flow.metric 0),
      A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧
        (K.toSmallBased p hkappa hnoncollapsed hnormalized).base ∈ A.core) :
    ∃ A : CapCertificate (K.flow.metric 0),
      A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core := by
  obtain ⟨A, hepsilon, hconstant, hp⟩ := hcap
  exact ⟨K.flow.capFromShrink 0 A, hepsilon, hconstant, hp⟩

theorem strongNeck_of_toSmallBased {t epsilon : ℝ}
    (hneck : ∃ A : StrongEvolvingNeck
        (K.toSmallBased p hkappa hnoncollapsed hnormalized).flow t epsilon,
      A.center = (K.toSmallBased p hkappa hnoncollapsed hnormalized).base) :
    ∃ A : StrongEvolvingNeck K t epsilon, A.center = p := by
  obtain ⟨A, hcenter⟩ := hneck
  refine ⟨A.ofPullbackFlow (K := K)
    (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M) rfl, ?_⟩
  change (equivShrink M).symm A.center = p
  simpa only [toSmallBased_base, Equiv.symm_apply_apply] using
    congrArg (equivShrink M).symm hcenter

end PoincareConjecture.AncientKappaSolution
