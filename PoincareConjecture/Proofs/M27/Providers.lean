import PoincareConjecture.Proofs.M27
import PoincareConjecture.Proofs.M16
import PoincareConjecture.Proofs.M19
import PoincareConjecture.Proofs.M20.Providers
import PoincareConjecture.Proofs.M22.Providers
import PoincareConjecture.Proofs.M23.Providers
import PoincareConjecture.Proofs.M24
import PoincareConjecture.Proofs.M25
import PoincareConjecture.Proofs.M26.Providers








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m27PredecessorsFromMilestones : M27KappaAlternativePredecessors.{u} := by
  let D16 : AncientKappaStructuralTheory.{u} 3 := Classical.choice
    (ancientKappaStructuralConsequences 3 ricciFlowCurvatureTheory
      differentialHarnackAncientTheory_from_M04
      (generalizedParabolicRescaling_from_M12 3))
  let C22 : UniversalNoncollapsingConclusion.{u} 3 :=
    Classical.choice (m22UniversalNoncollapsingFromMilestones 3)
  let T25 : RepairedNeckCapTopologyTheory.{u} := Classical.choice
    m25NeckCapTopology
  let T26 : RepairedCanonicalNeighborhoodTheory.{u} :=
    m26CanonicalNeighborhoodsFromMilestones
  refine {
    tensor_calculus := @LeviCivitaData.curvatureTensorCalculus
    scalar_regular := @RicciFlow.contMDiffOn_scalarCurvature 3
    scalar_evolution := @RicciFlow.hasDerivWithinAt_scalarCurvature 3
    curvature_evolution := @RicciFlow.hasDerivWithinAt_curvatureTensor 3
    past_norm_le_scalar := ?_
    normalization := ?_
    two_dimensional_classification := ?_
    universal_noncollapsing := ⟨C22.data.universal_kappa, C22.data.universal_kappa_pos,
      @C22.nonround_is_universally_noncollapsed⟩
    normalized_compactness := m23NormalizedKappaCompactnessFromMilestones
    model_refinement := ?_
    separating_neck_tube := ⟨T25.epsilon₀, T25.epsilon₀_pos,
      T25.epsilon₀_le_one_two_hundred, @T25.a19⟩
    global_neck_cap := ⟨T25.epsilon₀, T25.epsilon₀_pos,
      T25.epsilon₀_le_one_two_hundred, @T25.a25⟩
    noncompact_alternatives := T26.corollary_9_88
    compact_alternatives := T26.theorem_9_89
  }
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (D16.structural M K).past_norm_le_scalar
  · intro M _ _ _ _ _ _ _ _ _ K p b hb
    exact ⟨(D16.structural M K).normalization p b hb⟩
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (twoDimensionalAncientAndShrinkingSolitonClassification
      (m20TwoDimensionalPredecessors (N := M))).ancient_classification K
  · intro M _ _ _ _ _ _ _ _ _ S G input
    exact m24ModelCertificates input

theorem m27KappaAlternativesFromMilestones :
    RepairedKappaAlternativeTheory.{u} :=
  m27KappaAlternatives m27PredecessorsFromMilestones

end PoincareConjecture
