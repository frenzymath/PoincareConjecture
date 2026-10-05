import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Small
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Cover
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Shrink
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.StrongNeck

/-!
# Based solutions on the small carrier

A scalar-normalized ancient solution gives an actual based solution on its
shrunk carrier. Compactness, caps, and centered strong necks return through
the same shrinking diffeomorphism, with their parameters unchanged.

Reference: Morgan--Tian, Claim 9.90, p. 241 (`MT2007`).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.AncientKappaSolution

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

/-- The actual normalized flow on the small carrier used by compactness. -/
def toSmallBased : BasedKappaSolution kappa :=
  ScalarDerivatives.smallBasedKappaSolution K p kappa hkappa hnoncollapsed hnormalized

@[simp] theorem toSmallBased_flow :
    (K.toSmallBased p hkappa hnoncollapsed hnormalized).flow.flow = K.flow.shrink := rfl

@[simp] theorem toSmallBased_base :
    (K.toSmallBased p hkappa hnoncollapsed hnormalized).base = equivShrink M p := rfl

/-- Shrinking the carrier preserves compactness of the whole manifold. -/
theorem toSmallBased_isCompact (hcompact : IsCompact (univ : Set M)) :
    IsCompact (univ : Set
      (K.toSmallBased p hkappa hnoncollapsed hnormalized).carrier.carrier) := by
  simpa only [image_univ, EquivLike.range_eq_univ] using
    hcompact.image (Poincare.Topology.SecondCountable.homeomorphShrink M).continuous

/-- An open projective-plane collar on the small carrier would return to an
open collar on the original carrier through the shrinking homeomorphism. -/
theorem toSmallBased_noEmbeddedTrivialNormalProjectivePlane
    (hno : NoEmbeddedTrivialNormalProjectivePlane K) :
    NoEmbeddedTrivialNormalProjectivePlane
      (K.toSmallBased p hkappa hnoncollapsed hnormalized).flow := by
  rintro ⟨f, hf⟩
  exact hno ⟨(Poincare.Topology.SecondCountable.homeomorphShrink M).symm ∘ f,
    (Poincare.Topology.SecondCountable.homeomorphShrink M).symm.isOpenEmbedding.comp hf⟩

/-- A cap containing the based point in its core returns to the original
flow with the same epsilon and the same bound for its constant. -/
theorem cap_of_toSmallBased {epsilon C : ℝ}
    (hcap : ∃ A : CapCertificate
        ((K.toSmallBased p hkappa hnoncollapsed hnormalized).flow.flow.metric 0),
      A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧
        (K.toSmallBased p hkappa hnoncollapsed hnormalized).base ∈ A.core) :
    ∃ A : CapCertificate (K.flow.metric 0),
      A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core := by
  obtain ⟨A, hepsilon, hconstant, hp⟩ := hcap
  exact ⟨K.flow.capFromShrink 0 A, hepsilon, hconstant, hp⟩

/-- A strong neck centered at the based point returns with its full backward
time cylinder and epsilon to the original ancient solution. -/
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

end PoincareMT.AncientKappaSolution
