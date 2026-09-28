import PoincareConjecture.Proofs.M45.Ch9_Models.EvolvingCylinderTimeJets
import PoincareConjecture.Proofs.M45.Ch9_Models.EvolvingCylinderScalar
import Mathlib.Topology.MetricSpace.Thickening










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

open M44 SpacetimeBounds

noncomputable local instance marginCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance marginCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance marginTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance marginTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

noncomputable local instance marginJetArrayNormedGroup :
    NormedAddCommGroup (Fin 3 → MetricTwoJet 3) := Pi.normedAddCommGroup

noncomputable local instance marginJetArrayNormedSpace :
    NormedSpace ℝ (Fin 3 → MetricTwoJet 3) := Pi.normedSpace

noncomputable local instance marginFourJetNormedGroup :
    NormedAddCommGroup (ScalarMetricFourJet 3) := Prod.normedAddCommGroup

noncomputable local instance marginFourJetNormedSpace :
    NormedSpace ℝ (ScalarMetricFourJet 3) := Prod.normedSpace




def evolvingCylinderScalarRegion : Set (ScalarMetricFourJet 3) :=
  {J | J.1.1.IsInvertible ∧ (1 / 4 : ℝ) < jetScalarCurvature J.1 ∧
    |jetScalarLaplacian J| < (1 / 100 : ℝ)}



theorem isOpen_evolvingCylinderScalarRegion : IsOpen evolvingCylinderScalarRegion := by
  rw [isOpen_iff_mem_nhds]
  intro J hJ
  have hinv := ((isOpen_ricciFlowOperator_domain 3).preimage continuous_fst).mem_nhds hJ.1
  have hscalar := ((contDiffAt_jetScalarCurvature hJ.1).continuousAt.comp
    continuousAt_fst).eventually (lt_mem_nhds hJ.2.1)
  have hlap := (continuousAt_jetScalarLaplacian hJ.1).abs.eventually
    (gt_mem_nhds hJ.2.2)
  filter_upwards [hinv, hscalar, hlap] with J' hI hS hL
  exact ⟨hI, hS, hL⟩




theorem model_evolvingCylinder_mem_scalarRegion {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 0) :
    scalarMetricFourJet (evolvingCylinderModelField t) 0 ∈ evolvingCylinderScalarRegion := by
  have htone : t < 1 := lt_of_le_of_lt ht.2 (by norm_num)
  refine ⟨model_evolvingCylinderField_isInvertible htone 0, ?_, ?_⟩
  · change (1 / 4 : ℝ) < jetScalarCurvature (metricTwoJet (evolvingCylinderModelField t) 0)
    rw [model_evolvingCylinder_scalar htone, inv_eq_one_div]
    apply (lt_div_iff₀ (sub_pos.mpr htone)).2
    linarith [ht.1]
  · rw [model_evolvingCylinder_scalarLaplacian htone]
    norm_num

set_option synthInstance.maxHeartbeats 100000 in




theorem exists_uniform_evolvingCylinder_scalar_margin :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Icc (-1 : ℝ) 0, ∀ J : ScalarMetricFourJet 3,
      ‖J - scalarMetricFourJet (evolvingCylinderModelField t) 0‖ ≤ delta →
        J.1.1.IsInvertible ∧ (1 / 4 : ℝ) < jetScalarCurvature J.1 ∧
          |jetScalarLaplacian J| < (1 / 100 : ℝ) := by
  let K : Set (ScalarMetricFourJet 3) :=
    (fun t => scalarMetricFourJet (evolvingCylinderModelField t) 0) '' Icc (-1 : ℝ) 0
  have hK : IsCompact K := isCompact_Icc.image (continuous_model_evolvingCylinder_fourJet 0)
  have hsub : K ⊆ evolvingCylinderScalarRegion := by
    rintro _ ⟨t, ht, rfl⟩
    exact model_evolvingCylinder_mem_scalarRegion ht
  obtain ⟨delta, hdelta, hinside⟩ :=
    hK.exists_cthickening_subset_open isOpen_evolvingCylinderScalarRegion hsub
  refine ⟨delta, hdelta, ?_⟩
  intro t ht J hnear
  apply hinside
  exact Metric.mem_cthickening_of_dist_le J
    (scalarMetricFourJet (evolvingCylinderModelField t) 0) delta K ⟨t, ht, rfl⟩
    (by simpa only [dist_eq_norm] using hnear)

end PoincareConjecture.M45
