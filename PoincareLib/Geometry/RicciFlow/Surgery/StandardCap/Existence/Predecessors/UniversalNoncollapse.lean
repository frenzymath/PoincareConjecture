import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Proof
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Harnack
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.PointedCompactness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.LGeodesics
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.ReducedLength
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.ReducedVolume
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.OrdinaryFlow
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Predecessors
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Proof
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Noncollapse
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.BlowupSetup
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Soliton
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.AsymptoticVolume

/-!
# M22 providers from the earlier milestone theorems

Each field is an applied earlier output. Ordinary windows retain their
selected M08/M09 witnesses; M20 returns a classified limit for the same
sequence. These checked theorem proofs add no admission or data definition.
See reviews/contracts/2026-09-15-m22-complete-contract.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Supply all 21 services from their actual earlier producing theorems. -/
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

/-- Apply the existing complete M22 obligation with all earlier services supplied. -/
theorem m22UniversalNoncollapsingFromMilestones (n : ℕ) :
    Nonempty (UniversalNoncollapsingConclusion.{u} n) :=
  m22UniversalNoncollapsingAndZeroAVR n (m22PredecessorsFromMilestones n)

end PoincareMT
