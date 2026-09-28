import PoincareConjecture.Proofs.M23
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M06
import PoincareConjecture.Proofs.M07
import PoincareConjecture.Proofs.M13
import PoincareConjecture.Proofs.M16
import PoincareConjecture.Proofs.M19
import PoincareConjecture.Proofs.M20.Providers
import PoincareConjecture.Proofs.M21
import PoincareConjecture.Proofs.M22.Providers

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

theorem m23PredecessorsFromMilestones : M23NormalizedKappaCompactnessPredecessors := by
  let D16 : AncientKappaStructuralTheory.{0} 3 := Classical.choice
    (ancientKappaStructuralConsequences 3 ricciFlowCurvatureTheory
      differentialHarnackAncientTheory_from_M04 (generalizedParabolicRescaling_from_M12 3))
  let C22 : UniversalNoncollapsingConclusion.{0} 3 :=
    Classical.choice (m22UniversalNoncollapsingFromMilestones 3)
  refine {
    tensor_calculus := @LeviCivitaData.curvatureTensorCalculus
    curvature_norm_zero := @LeviCivitaData.curvatureDerivativeNorm_zero
    scalar_regular := @RicciFlow.contMDiffOn_scalarCurvature 3
    scalar_evolution := @RicciFlow.hasDerivWithinAt_scalarCurvature 3
    curvature_evolution := @RicciFlow.hasDerivWithinAt_curvatureTensor 3
    ricci_evolution := @RicciFlow.hasDerivWithinAt_ricci 3
    local_derivative_estimates := local_curvatureDerivative_bound 3
    scalar_zero_rigidity := @RicciFlow.flat_of_scalarCurvature_eq_zero
    pointed_compactness := ?_
    ordinary_rescaling := (generalizedParabolicRescaling_from_M12 3).ordinary_flow
    scalar_pos := ?_
    scalar_monotone := ?_
    past_norm_le_scalar := ?_
    ball_monotone := ?_
    two_dimensional_classification := ?_
    ratio_antitone := ?_
    zero_avr := ?_
  }
  · intro T' T _ _ H
    exact pointedRicciFlowCompactness_from_M04 H
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (D16.structural M K).scalar_pos
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (D16.structural M K).scalar_monotone
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (D16.structural M K).past_norm_le_scalar
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (D16.structural M K).ball_monotone
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (twoDimensionalAncientAndShrinkingSolitonClassification
      (m20TwoDimensionalPredecessors (N := M))).ancient_classification K
  · intro M _ _ _ _ _ _ _ _ _ K t ht
    obtain ⟨V⟩ := (m21AsymptoticVolumeRatioFromMilestones 3).slice K t ht
    exact V.ratio_antitone
  · intro M _ _ _ _ _ _ _ _ _ K
    exact C22.asymptotic_volume_ratio_zero K

theorem m23NormalizedKappaCompactnessFromMilestones (N : NormalizedKappaCompactnessData) :
    Nonempty (RedesignNormalizedKappaCompactnessConclusion N) :=
  m23NormalizedKappaCompactness N m23PredecessorsFromMilestones

end PoincareConjecture
