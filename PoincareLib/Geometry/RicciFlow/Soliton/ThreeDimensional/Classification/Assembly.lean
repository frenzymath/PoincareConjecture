import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Classification
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Compact
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.Bounded
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification.Static

/-!
# Assembly of the three-dimensional classification theory

The actual-limit curvature bound closes the specified-sequence branch. Together
with the static soliton classification it gives the exact frozen M20 theorem
from the original predecessor services.
-/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientAsymptoticSolitonLimitData

/-- The compact/noncompact split reduces an actual M18 limit to its
classification certificate once the noncompact curvature-bound producer is
available. -/
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

/-- A bound on every specified actual M18 limit assembles the asymptotic
classification theory for a fixed ancient kappa-solution. -/
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

/-- Final M20 structure assembly from the static theorem and an asymptotic
classification producer. -/
theorem threeDimensionalClassificationTheory_of_asymptotic
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (hasymptotic : ∀ K : AncientKappaSolution 3 M,
      Nonempty (ThreeDimensionalAsymptoticClassificationTheory K)) :
    ThreeDimensionalClassificationTheory (M := M) := by
  refine { classify := ?_, asymptotic_classify := hasymptotic }
  intro S
  exact GradientShrinkingSolitonData.threeDimensionalClassificationData (M := M) S hP

/-- The frozen M20 classification, including the actual limit of each specified
ancient rescaling sequence and equality of its entire classified flow. -/
theorem threeDimensionalAncientAndShrinkingSolitonClassification
    (P : ThreeDimensionalClassificationPredecessors.{u}) :
    ThreeDimensionalClassificationTheory (M := M) := by
  apply threeDimensionalClassificationTheory_of_asymptotic P
  intro K
  apply K.threeDimensionalAsymptoticClassification P
  intro S L t ht
  exact L.bounded_curvature_threeDimensional P t ht

end PoincareMT
