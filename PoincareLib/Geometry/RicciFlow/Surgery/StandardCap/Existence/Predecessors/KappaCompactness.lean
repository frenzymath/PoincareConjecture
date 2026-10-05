import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Proof
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Harnack
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.PointedCompactness
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Predecessors
import PoincareLib.Geometry.RicciFlow.AncientKappa.Structure
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Soliton
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.AsymptoticVolume
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.UniversalNoncollapse

/-!
# M23 providers from earlier milestone theorems

The selected M16/M22 witnesses supply only the properties needed by M23.
The M19 certificate is on the actual supplied two-dimensional solution.
All choices occur inside checked theorem proofs, with no new admission.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

/-- Supply all 17 primitive services on the actual Type0 carriers. -/
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

/-- Apply the complete M23 obligation with every earlier service supplied. -/
theorem m23NormalizedKappaCompactnessFromMilestones (N : NormalizedKappaCompactnessData) :
    Nonempty (RedesignNormalizedKappaCompactnessConclusion N) :=
  m23NormalizedKappaCompactness N m23PredecessorsFromMilestones

end PoincareMT
