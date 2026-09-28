import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_FiniteScalarBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M45

open PoincareConjecture.M44 PoincareConjecture.SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance gradientCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance gradientCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance gradientTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance gradientTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

noncomputable local instance gradientJetArrayNormedGroup :
    NormedAddCommGroup (Fin 3 → MetricTwoJet 3) := Pi.normedAddCommGroup

noncomputable local instance gradientJetArrayNormedSpace :
    NormedSpace ℝ (Fin 3 → MetricTwoJet 3) := Pi.normedSpace

noncomputable local instance gradientFourJetNormedGroup :
    NormedAddCommGroup (ScalarMetricFourJet 3) := Prod.normedAddCommGroup

noncomputable local instance gradientFourJetNormedSpace :
    NormedSpace ℝ (ScalarMetricFourJet 3) := Prod.normedSpace



theorem continuousAt_model_jetScalarFirst {J : ScalarMetricFourJet 3}
    (hJ : J.1.1.IsInvertible) (i : Fin 3) :
    ContinuousAt (fun K : ScalarMetricFourJet 3 => jetScalarFirst K i) J := by
  have hD := ((contDiffAt_jetScalarCurvature hJ).fderiv_right
    (m := ∞) (by simp)).continuousAt
  exact (hD.comp continuousAt_fst).clm_apply
    ((continuous_apply i).continuousAt.comp continuousAt_snd.fst)



theorem model_abs_linear_le_coordinate_sum (L : E →L[ℝ] ℝ) (v : E) :
    |L v| ≤ (∑ i, |L (EuclideanSpace.basisFun (Fin 3) ℝ i)|) * ‖v‖ := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have heq : L v = ∑ i, inner ℝ (b i) v * L (b i) := by
    calc
      L v = L (∑ i, inner ℝ (b i) v • b i) := congrArg L (b.sum_repr' v).symm
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  rw [heq, Finset.sum_mul]
  calc
    _ ≤ ∑ i, |inner ℝ (b i) v * L (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |L (b i)| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs, b.norm_eq_one, one_mul] using
        norm_inner_le_norm (𝕜 := ℝ) (b i) v

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in




theorem exists_model_scalar_differential_bound_of_fourJet (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : RiemannianMetric 3 E) (D : LeviCivitaData g) (x : E),
      ‖scalarMetricFourJet g.euclideanCoefficients x‖ ≤ B →
      (∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner x v v) →
      ∀ v : E, g.inner x v v = 1 → |fderiv ℝ D.scalarCurvature x v| ≤ C := by
  let : FiniteDimensional ℝ (MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ (E →L[ℝ] MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] MetricCoefficient 3) := by infer_instance
  let : FiniteDimensional ℝ (MetricTwoJet 3) := by infer_instance
  let : FiniteDimensional ℝ (Fin 3 → MetricTwoJet 3) := by infer_instance
  let : FiniteDimensional ℝ (Fin 3 → Fin 3 → MetricTwoJet 3) := by infer_instance
  let : FiniteDimensional ℝ (ScalarMetricFourJet 3) := by infer_instance
  let : ProperSpace (ScalarMetricFourJet 3) :=
    FiniteDimensional.proper ℝ (ScalarMetricFourJet 3)
  let K : Set (ScalarMetricFourJet 3) :=
    {J | ‖J‖ ≤ B ∧ ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ J.1.1 v v}
  have hK : IsCompact K := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    constructor
    · apply (isClosed_le continuous_norm continuous_const).inter
      change IsClosed {J : ScalarMetricFourJet 3 |
        ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ J.1.1 v v}
      rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro v
      exact isClosed_le continuous_const
        ((continuous_fst.fst.clm_apply continuous_const).clm_apply continuous_const)
    · exact isBounded_iff_forall_norm_le.mpr ⟨B, fun _ hJ => hJ.1⟩
  let f (J : ScalarMetricFourJet 3) : ℝ := ∑ i, |jetScalarFirst J i|
  have hf : ContinuousOn f K := by
    intro J hJ
    have hi := CoordinateTransition.isInvertible_of_uniformEllipticity
      (show (0 : ℝ) < 1 / 2 by norm_num) hJ.2
    have hcont : ContinuousAt f J := tendsto_finsetSum _ fun i _ =>
      (continuousAt_model_jetScalarFirst hi i).abs
    exact hcont.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨2 * max C 1, mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one
    (le_max_right _ _)), ?_⟩
  intro g D x hjets hell v hv
  have hvnorm : ‖v‖ ≤ 2 := by
    have h := hell v
    rw [hv] at h
    nlinarith [norm_nonneg v]
  have hsum : (∑ i, |fderiv ℝ D.scalarCurvature x
      (EuclideanSpace.basisFun (Fin 3) ℝ i)|) ≤ max C 1 := by
    have h := hC _ ⟨hjets, hell⟩
    have hnonneg : 0 ≤ f (scalarMetricFourJet g.euclideanCoefficients x) :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at h
    dsimp only [f] at h
    simp_rw [jetScalarFirst_scalarMetricFourJet D] at h
    exact h.trans (le_max_left _ _)
  calc
    _ ≤ (∑ i, |fderiv ℝ D.scalarCurvature x
        (EuclideanSpace.basisFun (Fin 3) ℝ i)|) * ‖v‖ :=
      model_abs_linear_le_coordinate_sum _ _
    _ ≤ max C 1 * 2 := mul_le_mul hsum hvnorm (norm_nonneg _)
      (le_trans zero_le_one (le_max_right _ _))
    _ = _ := mul_comm _ _



theorem exists_model_scalar_differential_bound_of_coordinate_jets (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : RiemannianMetric 3 E) (D : LeviCivitaData g) (x : E),
      (∀ j ≤ 4, ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ B) →
      (∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner x v v) →
      ∀ v : E, g.inner x v v = 1 → |fderiv ℝ D.scalarCurvature x v| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_model_scalar_differential_bound_of_fourJet B
  refine ⟨C, hC, ?_⟩
  intro g D x hjets hell
  exact hbound g D x
    (norm_scalarMetricFourJet_le (g.contDiffAt_euclideanCoefficients x) hjets) hell

end PoincareConjecture.M45
