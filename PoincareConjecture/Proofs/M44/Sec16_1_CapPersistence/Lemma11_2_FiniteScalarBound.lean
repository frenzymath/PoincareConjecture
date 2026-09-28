import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarFourJet
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RicciJetNorm











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open PoincareConjecture.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)


noncomputable local instance finiteCoefficientNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricCoefficient n) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance finiteCoefficientNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricCoefficient n) := ContinuousLinearMap.toNormedSpace

noncomputable local instance finiteTwoJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricTwoJet n) := Prod.normedAddCommGroup

noncomputable local instance finiteTwoJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricTwoJet n) := Prod.normedSpace

noncomputable local instance finiteJetArrayNormedGroup (n : ℕ) :
    NormedAddCommGroup (Fin n → MetricTwoJet n) := Pi.normedAddCommGroup

noncomputable local instance finiteJetArrayNormedSpace (n : ℕ) :
    NormedSpace ℝ (Fin n → MetricTwoJet n) := Pi.normedSpace

noncomputable local instance finiteFourJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (ScalarMetricFourJet n) := Prod.normedAddCommGroup

noncomputable local instance finiteFourJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (ScalarMetricFourJet n) := Prod.normedSpace

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in





theorem exists_scalar_evolution_bound_of_fourJet
    (n : ℕ) {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : RiemannianMetric n (E n))
      (D : LeviCivitaData g) (x : E n),
      ‖scalarMetricFourJet g.euclideanCoefficients x‖ ≤ B →
      (∀ v : E n, a * ‖v‖ ^ 2 ≤ g.inner x v v) →
        |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤ C := by
  let : FiniteDimensional ℝ (MetricCoefficient n) := by infer_instance
  let : FiniteDimensional ℝ (E n →L[ℝ] MetricCoefficient n) := by infer_instance
  let : FiniteDimensional ℝ (E n →L[ℝ] E n →L[ℝ] MetricCoefficient n) := by infer_instance
  let : FiniteDimensional ℝ (MetricTwoJet n) := by infer_instance
  let : FiniteDimensional ℝ (Fin n → MetricTwoJet n) := by infer_instance
  let : FiniteDimensional ℝ (Fin n → Fin n → MetricTwoJet n) := by infer_instance
  let : FiniteDimensional ℝ (ScalarMetricFourJet n) := by infer_instance
  let : ProperSpace (ScalarMetricFourJet n) :=
    FiniteDimensional.proper ℝ (ScalarMetricFourJet n)
  let K : Set (ScalarMetricFourJet n) :=
    {J | ‖J‖ ≤ B ∧ ∀ v : E n, a * ‖v‖ ^ 2 ≤ J.1.1 v v}
  have hK : IsCompact K := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    constructor
    · apply (isClosed_le continuous_norm continuous_const).inter
      change IsClosed {J : ScalarMetricFourJet n | ∀ v : E n, a * ‖v‖ ^ 2 ≤ J.1.1 v v}
      rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro v
      exact isClosed_le continuous_const
        ((continuous_fst.fst.clm_apply continuous_const).clm_apply continuous_const)
    · exact isBounded_iff_forall_norm_le.mpr ⟨B, fun _ hJ => hJ.1⟩
  let f (J : ScalarMetricFourJet n) : ℝ :=
    |jetScalarLaplacian J| + 2 * (n : ℝ) ^ 2 * (‖jetRicciBilinear J.1‖ / a) ^ 2
  have hf : ContinuousOn f K := by
    intro J hJ
    have hi := CoordinateTransition.isInvertible_of_uniformEllipticity ha hJ.2
    have hL := (continuousAt_jetScalarLaplacian hi).abs
    have hR := ((contDiffAt_jetRicciBilinear hi).continuousAt.comp continuousAt_fst).norm
    exact (hL.add (((hR.div_const a).pow 2).const_mul (2 * (n : ℝ) ^ 2))).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro g D x hnorm hell
  have hricci : 0 ≤ D.ricciNormSq x :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound := ricciNormSq_le_jetRicciBilinear D x ha hell
  calc
    _ ≤ |D.laplacian D.scalarCurvature x| + |2 * D.ricciNormSq x| := abs_add_le _ _
    _ = |D.laplacian D.scalarCurvature x| + 2 * D.ricciNormSq x := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hricci)]
    _ ≤ |D.laplacian D.scalarCurvature x| +
        2 * (n : ℝ) ^ 2 * (‖jetRicciBilinear
          (metricTwoJet g.euclideanCoefficients x)‖ / a) ^ 2 := by linarith
    _ = f (scalarMetricFourJet g.euclideanCoefficients x) := by
      dsimp [f]
      rw [jetScalarLaplacian_scalarMetricFourJet D]
      rfl
    _ ≤ ‖f (scalarMetricFourJet g.euclideanCoefficients x)‖ := le_abs_self _
    _ ≤ C := hC _ ⟨hnorm, hell⟩
    _ ≤ max C 1 := le_max_left _ _




theorem norm_iteratedFDeriv_metricTwoJet_le {n m : ℕ}
    {B : E n → MetricCoefficient n} {x : E n} (hB : ContDiffAt ℝ ∞ B x)
    {C : ℝ} (hbound : ∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j B x‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (metricTwoJet B) x‖ ≤ C := by
  have hB' := hB.fderiv_right (m := ∞) (by simp)
  have hB'' := hB'.fderiv_right (m := ∞) (by simp)
  change ‖iteratedFDeriv ℝ m (fun y => (B y, fderiv ℝ B y,
    fderiv ℝ (fderiv ℝ B) y)) x‖ ≤ C
  rw [iteratedFDeriv_prodMk hB (hB'.prodMk hB'') (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le (hbound m (by omega))
  rw [iteratedFDeriv_prodMk hB' hB'' (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod,
    norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  exact max_le (hbound (m + 1) (by omega)) (hbound (m + 1 + 1) (by omega))

set_option maxHeartbeats 800000 in




theorem norm_scalarMetricFourJet_le {n : ℕ}
    {B : E n → MetricCoefficient n} {x : E n} (hB : ContDiffAt ℝ ∞ B x)
    {C : ℝ} (hbound : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j B x‖ ≤ C) :
    ‖scalarMetricFourJet B x‖ ≤ C := by
  have hJ (m : ℕ) (hm : m ≤ 2) : ‖iteratedFDeriv ℝ m (metricTwoJet B) x‖ ≤ C :=
    norm_iteratedFDeriv_metricTwoJet_le hB (fun j hj => hbound j (by omega))
  have hzero := hJ 0 (by omega)
  have hone := hJ 1 (by omega)
  have htwo := hJ 2 le_rfl
  rw [norm_iteratedFDeriv_zero] at hzero
  rw [norm_iteratedFDeriv_one] at hone
  have hsecond : ‖fderiv ℝ (fderiv ℝ (metricTwoJet B)) x‖ =
      ‖iteratedFDeriv ℝ 2 (metricTwoJet B) x‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact norm_coordinateDerivativeArray_le (EuclideanSpace.basisFun (Fin n) ℝ)
    (fun i => (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i |>.le)
    _ _ _ hzero hone (hsecond.le.trans htwo)





theorem exists_scalar_evolution_bound_of_coordinate_jets
    (n : ℕ) {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : RiemannianMetric n (E n))
      (D : LeviCivitaData g) (x : E n),
      (∀ j ≤ 4, ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ B) →
      (∀ v : E n, a * ‖v‖ ^ 2 ≤ g.inner x v v) →
        |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_scalar_evolution_bound_of_fourJet n ha B
  refine ⟨C, hC, ?_⟩
  intro g D x hjets hell
  exact hbound g D x
    (norm_scalarMetricFourJet_le (g.contDiffAt_euclideanCoefficients x) hjets) hell

end PoincareConjecture.M44
