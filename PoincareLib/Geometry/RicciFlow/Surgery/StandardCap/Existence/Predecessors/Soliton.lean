import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Classification
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Harnack
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.PointedCompactness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.ReducedVolume
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Predecessors
import PoincareLib.Geometry.RicciFlow.AncientKappa.Structure
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.AsymptoticSoliton

/-!
# M20 providers from the earlier milestone theorems

The M16 whole-past bound supplies the exact finite-window hypotheses of
M08--M10. Apply M18 separately in dimensions two and three, then supply M19
before constructing M20's predecessor record. Every construction stays in a
theorem proof; no admitted-dependent data definition or new admission is used.

The natural-language application derivation and source boundaries are in
`reviews/contracts/2026-09-15-m20-provider-audit.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Supply every M18 service on the given ancient solution and its actual flow. -/
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

/-- Apply M18 to each exact input sequence in the specified dimension. -/
theorem m20AsymptoticSolitonProvider (n : ℕ) :
    AncientAsymptoticSolitonTheory.{u} n := by
  apply ancientAsymptoticSolitonTheory_from_predecessors n
  intro M _ _ _ _ _ _ _ _ _ K
  exact m20AsymptoticPredecessors K

/-- M19 receives dimension-two compactness and the actual dimension-two M18 service. -/
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

/-- Construct all six M20 services by applying their earlier producing theorems. -/
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

/-- M20's existing full conclusion, with every predecessor supplied. -/
theorem m20ClassificationFromMilestones
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] :
    ThreeDimensionalClassificationTheory (M := M) :=
  threeDimensionalAncientAndShrinkingSolitonClassification m20ClassificationPredecessors

end PoincareMT
