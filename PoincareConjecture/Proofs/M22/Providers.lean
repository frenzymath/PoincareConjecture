import PoincareConjecture.Proofs.M22
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M06
import PoincareConjecture.Proofs.M07
import PoincareConjecture.Proofs.M08
import PoincareConjecture.Proofs.M09
import PoincareConjecture.Proofs.M10
import PoincareConjecture.Proofs.M12
import PoincareConjecture.Proofs.M13
import PoincareConjecture.Proofs.M14
import PoincareConjecture.Proofs.M15.Providers
import PoincareConjecture.Proofs.M17
import PoincareConjecture.Proofs.M19
import PoincareConjecture.Proofs.M20.Providers
import PoincareConjecture.Proofs.M21










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


theorem m22PredecessorsFromMilestones (n : ℕ) :
    M22UniversalNoncollapsingPredecessors.{u} n := by
  have h12 : GeneralizedRicciGaugeTheory.{u} 3 :=
    generalizedRicciGaugeGeometry_from_M03_M04_M11 3
  have h13 : GeneralizedParabolicRescalingTheory.{u} 3 :=
    generalizedParabolicRescaling_from_M12 3
  have h14 : GeneralizedLGeometryTheory.{u} 3 :=
    generalizedLGeometryTheory h12 h13 ricciFlowCurvatureTheory
  have O : M14OrdinaryProviders.{u} 3 := m15OrdinaryProvidersFromMilestones 3
  have h17 : AncientBlowupSetupTheory.{u} 3 := by
    refine ancientBlowupSequenceSetupTheory 3 ?_ h13
    intro M _ _ _ _ _ _ _ _ _ K _reference
    exact (m20AsymptoticPredecessors K).reduced_volume
  refine {
    tensor_calculus := @LeviCivitaData.curvatureTensorCalculus
    curvature_norm_zero := @LeviCivitaData.curvatureDerivativeNorm_zero
    scalar_regular := @RicciFlow.contMDiffOn_scalarCurvature
    scalar_evolution := @RicciFlow.hasDerivWithinAt_scalarCurvature
    curvature_evolution := @RicciFlow.hasDerivWithinAt_curvatureTensor
    ricci_evolution := @RicciFlow.hasDerivWithinAt_ricci
    local_derivative_estimates := @local_curvatureDerivative_bound
    metric_edist_transport :=
      differentialHarnackAncientTheory_from_M04.metric_edist_transport
    ancient_differential :=
      differentialHarnackAncientTheory_from_M04.ancient_differential
    pointed_compactness := ?_
    ordinary_windows := O
    ordinary_product := h12.ordinary_flow
    ordinary_rescaling := ?_
    metric_homothety := ?_
    exponential := ?_
    ordinary_capture := ?_
    noncollapse_generalized :=
      (noncollapsingGeneralizedAndCompact_from_predecessors 3).generalized.uniform
    blowup_setup := h17
    two_dimensional_compact := ?_
    classified_limit := ?_
    volume_ratio := m21AsymptoticVolumeRatioFromMilestones
  }
  · intro d T' T _ _ H
    exact pointedRicciFlowCompactness_from_M04 H
  · intro d
    exact (generalizedParabolicRescaling_from_M12 d).ordinary_flow
  · intro d
    exact (generalizedParabolicRescaling_from_M12 d).metric_homothety
  · intro X _ time I G
    obtain ⟨Q⟩ := h14.conclusion X time I G
    exact ⟨Q.exponential⟩
  · intro X _ time I G O'
    obtain ⟨Q⟩ := h14.conclusion X time I G
    exact Q.ordinary_capture O'
  · intro M _ _ _ _ _ _ _ _ _ K
    obtain ⟨C⟩ :=
      (twoDimensionalAncientAndShrinkingSolitonClassification
        (m20TwoDimensionalPredecessors (N := M))).ancient_classification K
    exact C.compact
  · intro M _ _ _ _ _ _ _ _ _ K S
    obtain ⟨A⟩ := (m20ClassificationFromMilestones (M := M)).asymptotic_classify K
    exact A.classify S


theorem m22UniversalNoncollapsingFromMilestones (n : ℕ) :
    Nonempty (UniversalNoncollapsingConclusion.{u} n) :=
  m22UniversalNoncollapsingAndZeroAVR n (m22PredecessorsFromMilestones n)

end PoincareConjecture
