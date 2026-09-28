import PoincareConjecture.Proofs.M20
import PoincareConjecture.Proofs.M06
import PoincareConjecture.Proofs.M07
import PoincareConjecture.Proofs.M10
import PoincareConjecture.Proofs.M13
import PoincareConjecture.Proofs.M16
import PoincareConjecture.Proofs.M18













set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


theorem m20AsymptoticPredecessors
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) : AncientAsymptoticSolitonPredecessors K := by
  obtain ⟨D⟩ := ancientKappaStructuralConsequences n ricciFlowCurvatureTheory
    differentialHarnackAncientTheory_from_M04 (generalizedParabolicRescaling_from_M12 n)
  have hzero : (0 : ℝ) ∈ Set.Iic 0 := show (0 : ℝ) ≤ 0 from le_rfl
  have hwindow (R : ℝ) : Set.Icc (0 - R) 0 ⊆ Set.Iic 0 :=
    fun _ ht => ht.2
  have hcurvature (R : ℝ) :
      CompleteBoundedCurvatureOn K.flow (Set.Icc (0 - R) 0) := by
    obtain ⟨C, hC, hbound⟩ := (D.structural M K).whole_past_bound 0 le_rfl
    exact ⟨fun t ht => K.complete t ht.2,
      C, hC.le, fun t ht x => hbound t ht.2 x⟩
  refine {
    structural := ⟨D⟩
    harnack := differentialHarnackAncientTheory_from_M04
    pointed_compactness := ?_
    l_geometry := ?_
    reduced_length := ?_
    reduced_volume := ?_
  }
  · intro T' T _ _ H
    exact pointedRicciFlowCompactness_from_M04 H
  · intro R hR
    exact lGeodesicExistenceAndVariation_from_M04 K.flow 0 R hzero hR
      (hwindow R) (hcurvature R)
  · intro R hR
    exact reducedLengthDifferentialInequalities_from_M04_M08 K.flow 0 R hzero hR
      (hwindow R) (hcurvature R)
  · intro R hR
    exact reducedVolumeMonotonicity_from_M08_M09 K.flow 0 R hzero hR
      (hwindow R) (hcurvature R)


theorem m20AsymptoticSolitonProvider (n : ℕ) :
    AncientAsymptoticSolitonTheory.{u} n := by
  apply ancientAsymptoticSolitonTheory_from_predecessors n
  intro M _ _ _ _ _ _ _ _ _ K
  exact m20AsymptoticPredecessors K


theorem m20TwoDimensionalPredecessors
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
    [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
    [T2Space N] [T3Space N] [SecondCountableTopology N] [ConnectedSpace N] :
    TwoDimensionalClassificationPredecessors (M := N) := by
  refine ⟨?_, ?_⟩
  · intro T' T _ _ H
    exact pointedRicciFlowCompactness_from_M04 H
  · intro K S
    exact (m20AsymptoticSolitonProvider 2).limits N K S


theorem m20ClassificationPredecessors :
    ThreeDimensionalClassificationPredecessors.{u} := by
  refine {
    local_flow := m20CompactLocalFlowProvider_from_M03
    curvature := ricciFlowCurvatureTheory
    harnack := differentialHarnackAncientTheory_from_M04
    pointed_compactness := ?_
    m18 := m20AsymptoticSolitonProvider 3
    two_dimensional := ?_
  }
  · intro n T' T _ _ H
    exact pointedRicciFlowCompactness_from_M04 H
  · apply m20TwoDimensionalProvider_from_M19
    intro N _ _ _ _ _ _ _ _ _
    exact m20TwoDimensionalPredecessors (N := N)


theorem m20ClassificationFromMilestones
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] :
    ThreeDimensionalClassificationTheory (M := M) :=
  threeDimensionalAncientAndShrinkingSolitonClassification m20ClassificationPredecessors

end PoincareConjecture
