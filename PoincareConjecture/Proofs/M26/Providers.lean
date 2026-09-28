import PoincareConjecture.Proofs.M26
import PoincareConjecture.Proofs.M16
import PoincareConjecture.Proofs.M17
import PoincareConjecture.Proofs.M19
import PoincareConjecture.Proofs.M20.Providers
import PoincareConjecture.Proofs.M22.Providers
import PoincareConjecture.Proofs.M23.Providers
import PoincareConjecture.Proofs.M24
import PoincareConjecture.Proofs.M25










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m26BlowupSetupProvider_from_M17
    (hM10 : ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M) (_reference : M),
      AncientReducedVolumeMinimumProvider K)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3) :
    M26BlowupSetupProvider.{u} := by
  intro M _ _ _ _ _ _ _ _ _ K reference tau tau_pos tau_tendsto
  exact ancientBlowupSequenceSetup 3 M K reference tau tau_pos tau_tendsto
    (hM10 M K reference) hM13

theorem m26AsymptoticClassificationProvider_from_M20
    (p20 : ThreeDimensionalClassificationPredecessors.{u}) :
    M26AsymptoticClassificationProvider.{u} := by
  intro M _ _ _ _ _ _ _ _ _ K S
  obtain ⟨classification⟩ :=
    (threeDimensionalAncientAndShrinkingSolitonClassification p20).asymptotic_classify K
  exact classification.classify S

theorem m26NormalizedCompactnessProvider_from_M23
    (P : M23NormalizedKappaCompactnessPredecessors) :
    ∀ N : NormalizedKappaCompactnessData,
      Nonempty (RedesignNormalizedKappaCompactnessConclusion N) :=
  fun N => m23NormalizedKappaCompactness N P


theorem m26PredecessorsFromMilestones : M26CanonicalNeighborhoodPredecessors.{u} := by
  let D16 : AncientKappaStructuralTheory.{u} 3 := Classical.choice
    (ancientKappaStructuralConsequences 3 ricciFlowCurvatureTheory
      differentialHarnackAncientTheory_from_M04 (generalizedParabolicRescaling_from_M12 3))
  let C22 : UniversalNoncollapsingConclusion.{u} 3 :=
    Classical.choice (m22UniversalNoncollapsingFromMilestones 3)
  let T25 : RepairedNeckCapTopologyTheory.{u} := Classical.choice m25NeckCapTopology
  refine {
    tensor_calculus := @LeviCivitaData.curvatureTensorCalculus
    scalar_regular := @RicciFlow.contMDiffOn_scalarCurvature 3
    scalar_evolution := @RicciFlow.hasDerivWithinAt_scalarCurvature 3
    curvature_evolution := @RicciFlow.hasDerivWithinAt_curvatureTensor 3
    ricci_evolution := @RicciFlow.hasDerivWithinAt_ricci 3
    past_norm_le_scalar := ?_
    normalization := ?_
    blowup_setup := ?_
    two_dimensional_classification := ?_
    classified_limit := m26AsymptoticClassificationProvider_from_M20 m20ClassificationPredecessors
    universal_noncollapsing := ⟨C22.data.universal_kappa, C22.data.universal_kappa_pos,
      @C22.nonround_is_universally_noncollapsed⟩
    normalized_compactness := m23NormalizedKappaCompactnessFromMilestones
    model_refinement := ?_
    global_neck_cap := ⟨T25.epsilon₀, T25.epsilon₀_pos,
      T25.epsilon₀_le_one_two_hundred, @T25.a25⟩
  }
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (D16.structural M K).past_norm_le_scalar
  · intro M _ _ _ _ _ _ _ _ _ K p b hb
    exact ⟨(D16.structural M K).normalization p b hb⟩
  · apply m26BlowupSetupProvider_from_M17
    · intro M _ _ _ _ _ _ _ _ _ K _reference
      exact (m20AsymptoticPredecessors K).reduced_volume
    · exact generalizedParabolicRescaling_from_M12 3
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (twoDimensionalAncientAndShrinkingSolitonClassification
      (m20TwoDimensionalPredecessors (N := M))).ancient_classification K
  · intro M _ _ _ _ _ _ _ _ _ S G input
    exact m24ModelCertificates input


theorem m26CanonicalNeighborhoodsFromMilestones : RepairedCanonicalNeighborhoodTheory.{u} :=
  m26CanonicalNeighborhoods m26PredecessorsFromMilestones

end PoincareConjecture
