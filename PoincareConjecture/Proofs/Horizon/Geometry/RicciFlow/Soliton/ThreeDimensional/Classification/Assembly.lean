import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Classification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.Bounded
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification.Static








noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientAsymptoticSolitonLimitData




theorem classificationCertificate_of_compact_or_bound
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}
    (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    ThreeDimensionalAsymptoticClassificationCertificate S L := by
  classical
  by_cases hc : CompactSpace L.convergence.limit.carrier.carrier
  · letI : CompactSpace L.convergence.limit.carrier.carrier := hc
    exact L.classificationCertificate_of_compact hP.curvature
  · exact L.classificationCertificate_of_bounded_curvature hP hbound

end AncientAsymptoticSolitonLimitData



theorem AncientKappaSolution.threeDimensionalAsymptoticClassification
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (K : AncientKappaSolution 3 M)
    (hbound : ∀ (S : AncientRescalingSequence K)
      (L : AncientAsymptoticSolitonLimitData S) (t : ℝ), t < 0 →
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ x : L.convergence.limit.carrier.carrier,
          |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    Nonempty (ThreeDimensionalAsymptoticClassificationTheory K) := by
  refine ⟨{ classify := ?_ }⟩
  intro S
  obtain ⟨L⟩ := hP.m18.limits M K S
  exact ⟨L, L.classificationCertificate_of_compact_or_bound hP (hbound S L)⟩



theorem threeDimensionalClassificationTheory_of_asymptotic
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (hasymptotic : ∀ K : AncientKappaSolution 3 M,
      Nonempty (ThreeDimensionalAsymptoticClassificationTheory K)) :
    ThreeDimensionalClassificationTheory (M := M) := by
  refine { classify := ?_, asymptotic_classify := hasymptotic }
  intro S
  exact GradientShrinkingSolitonData.threeDimensionalClassificationData (M := M) S hP



theorem horizon_threeDimensionalAncientAndShrinkingSolitonClassification
    (P : ThreeDimensionalClassificationPredecessors.{u}) :
    ThreeDimensionalClassificationTheory (M := M) := by
  apply threeDimensionalClassificationTheory_of_asymptotic P
  intro K
  apply K.threeDimensionalAsymptoticClassification P
  intro S L t ht
  exact L.bounded_curvature_threeDimensional P t ht

end PoincareConjecture
