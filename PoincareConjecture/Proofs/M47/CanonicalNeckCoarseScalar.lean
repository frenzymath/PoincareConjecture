import PoincareConjecture.Proofs.M47.CanonicalNeckCoarseJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Equation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M47

open M36 M44 SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

noncomputable local instance coarseCoefficientNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricCoefficient n) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance coarseCoefficientNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricCoefficient n) := ContinuousLinearMap.toNormedSpace

noncomputable local instance coarseTwoJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricTwoJet n) := Prod.normedAddCommGroup

noncomputable local instance coarseTwoJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricTwoJet n) := Prod.normedSpace


theorem exists_scalar_bound_of_elliptic_twoJets
    (n : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : MetricTwoJet n, ‖J‖ ≤ H →
      (∀ v : E n, a * ‖v‖ ^ 2 ≤ J.1 v v) → |jetScalarCurvature J| ≤ C := by
  let : FiniteDimensional ℝ (MetricCoefficient n) := by infer_instance
  let : FiniteDimensional ℝ (E n →L[ℝ] MetricCoefficient n) := by infer_instance
  let : FiniteDimensional ℝ (E n →L[ℝ] E n →L[ℝ] MetricCoefficient n) := by infer_instance
  let : FiniteDimensional ℝ (MetricTwoJet n) := by infer_instance
  let : ProperSpace (MetricTwoJet n) := FiniteDimensional.proper ℝ (MetricTwoJet n)
  let K : Set (MetricTwoJet n) :=
    {J | ‖J‖ ≤ H ∧ ∀ v : E n, a * ‖v‖ ^ 2 ≤ J.1 v v}
  have hK : IsCompact K := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    constructor
    · apply (isClosed_le continuous_norm continuous_const).inter
      change IsClosed {J : MetricTwoJet n | ∀ v : E n, a * ‖v‖ ^ 2 ≤ J.1 v v}
      rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro v
      exact isClosed_le continuous_const
        ((continuous_fst.clm_apply continuous_const).clm_apply continuous_const)
    · exact isBounded_iff_forall_norm_le.mpr ⟨H, fun _ hJ => hJ.1⟩
  have hf : ContinuousOn (@jetScalarCurvature n) K := by
    intro J hJ
    have hi := CoordinateTransition.isInvertible_of_uniformEllipticity ha hJ.2
    exact (contDiffAt_jetScalarCurvature hi).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro J hJ hell
  exact (hC J ⟨hJ, hell⟩).trans (le_max_left _ _)


theorem exists_negativeCylinder_scalar_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {epsilon t : ℝ}, 0 < epsilon → epsilon ≤ 1 / 200 →
      t ∈ Icc (-1 : ℝ) 0 → ∀ {B : RoundCylinderTwoTensor},
      RoundCylinderClose epsilon t B → ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        |jetScalarCurvature (metricTwoJet (centeredCylinderMetric B z.1 z.2) 0)| ≤ C := by
  obtain ⟨H, _hH, hHbound⟩ := exists_negativeCylinder_twoJet_bound
  obtain ⟨C, hC, hbound⟩ := exists_scalar_bound_of_elliptic_twoJets 3
    (show 0 < (1 / 2 : ℝ) by norm_num) H
  refine ⟨C, hC, ?_⟩
  intro epsilon t hepsilon hsmall ht B hB z hz
  exact hbound _ (hHbound hepsilon hsmall ht hB z hz)
    (negativeCylinder_coefficient_lower hepsilon hsmall ht hB z hz)


theorem exists_negativeCylinder_realized_scalar_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {epsilon t : ℝ}, 0 < epsilon → epsilon ≤ 1 / 200 →
      t ∈ Icc (-1 : ℝ) 0 → ∀ {B : RoundCylinderTwoTensor},
      RoundCylinderClose epsilon t B → ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ (g : RiemannianMetric 3 (E 3)) (D : LeviCivitaData g),
        g.euclideanCoefficients =ᶠ[𝓝 0] centeredCylinderMetric B z.1 z.2 →
          |D.scalarCurvature 0| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_negativeCylinder_scalar_bound
  refine ⟨C, hC, ?_⟩
  intro epsilon t hepsilon hsmall ht B hB z hz g D hgerm
  rw [← jetScalarCurvature_metricTwoJet D, metricTwoJet_congr_of_eventuallyEq hgerm]
  exact hbound hepsilon hsmall ht hB z hz

end PoincareConjecture.Proofs.M47
