import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Bounds.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Noncompact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.MaximalBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem scalarRadius_pos (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    0 < (K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ) :=
  Real.rpow_pos_of_pos (C.scalarCurvature_pos ht x) _

theorem scalarRadius_inv_sq (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    ((K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))⁻¹ ^ (2 : ℕ) =
      (K.flow.connection t).scalarCurvature x := by
  have hR := C.scalarCurvature_pos ht x
  rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
    ← Real.rpow_mul hR.le]
  norm_num

theorem scalarRadius_ball_sup (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
      ((K.flow.metric t).ball x
        ((K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))) =
      ((K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))⁻¹ ^ (2 : ℕ) := by
  rw [C.scalarRadius_inv_sq ht x]
  apply C.scalarCurvatureSupOn_eq ht
  refine ⟨x, ?_⟩
  change (K.flow.metric t).edist x x < _
  simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
  exact ENNReal.ofReal_pos.mpr (C.scalarRadius_pos ht x)

theorem isCompact_closure_scalarRadius_ball (_C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    IsCompact (closure ((K.flow.metric t).ball x
      ((K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ)))) :=
  (K.flow.metric t).isCompact_closure_ball_of_metricComplete (K.complete t ht) x _

theorem scalarRadius_volume_lower_bound_of_noncollapsed
    (C : M27TwistedSphereLineFlowCertificate K)
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa : ℝ} (hnc : AncientKappaNoncollapsed K.flow kappa)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    ENNReal.ofReal (kappa *
      ((K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ)) ^ (3 : ℕ)) ≤
      calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball x
        ((K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))) := by
  apply hnc _ (C.scalarRadius_pos ht x) t ht x _ (C.scalarRadius_pos ht x) le_rfl
  intro s hs y _
  rw [abs_of_nonneg (show 0 ≤ (K.flow.connection s).curvatureTensorNorm y from
    Real.sqrt_nonneg _), C.scalarRadius_inv_sq ht x]
  exact (P.past_norm_le_scalar M K s t hs.2 ht y).trans_eq
    (C.scalarCurvature_eq ht y x)

theorem exists_universal_scalarRadius_volume_lower_bound
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        {K : AncientKappaSolution 3 M} (_C : M27TwistedSphereLineFlowCertificate K)
        (t : ℝ), t ≤ 0 → ∀ x : M,
        ENNReal.ofReal (kappa *
          ((K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ)) ^ (3 : ℕ)) ≤
          calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball x
            ((K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))) := by
  obtain ⟨kappa, hkappa, hnc⟩ := P.universal_noncollapsing
  refine ⟨kappa, hkappa, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K C t ht x
  exact C.scalarRadius_volume_lower_bound_of_noncollapsed P
    (hnc K (K.not_isRound_of_noncompact C.not_isCompact_univ)) ht x

theorem calibratedVolume_le_of_subset_ball
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {t : ℝ} (ht : t ≤ 0) (x : M) {r : ℝ} (hr : 0 < r)
    {U : Set M} (hU : U ⊆ (K.flow.metric t).ball x r) :
    calibratedMetricVolume (K.flow.metric t) U ≤
      ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 3 * r ^ (3 : ℕ)) := by
  have hRic (y : M) (v : TangentSpace (𝓡 3) y) :
      0 ≤ (K.flow.connection t).ricci y v v :=
    ((K.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (P.tensor_calculus 3 M (K.flow.metric t) (K.flow.connection t)) y
      (K.nonnegative_curvature_operator t ht y) v).1
  have hupper := (K.flow.metric t).ball_volume_div_pow_le_euclideanUnitBallVolume
    (K.flow.connection t) (by norm_num) (K.complete t ht) hRic x hr
  apply (MeasureTheory.measure_mono hU).trans
  rw [calibratedMetricVolume_eq_volumeMeasure,
    ← ENNReal.ofReal_toReal ((K.flow.metric t).ball_volume_ne_top_of_metricComplete
      (K.complete t ht) x r)]
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (pow_pos hr 3)).mp hupper)

theorem calibratedVolume_le_of_subset_scalarRadius_ball
    (C : M27TwistedSphereLineFlowCertificate K)
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {t : ℝ} (ht : t ≤ 0) (x : M) {A : ℝ} (hA : 0 < A)
    {U : Set M} (hU : U ⊆ (K.flow.metric t).ball x
      (A * (K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))) :
    calibratedMetricVolume (K.flow.metric t) U ≤
      ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 3 * A ^ (3 : ℕ)) *
        ENNReal.ofReal ((K.flow.connection t).scalarCurvature x ^ (-3 / 2 : ℝ)) := by
  have hvol := calibratedVolume_le_of_subset_ball P ht x
    (mul_pos hA (C.scalarRadius_pos ht x)) hU
  have heq : (A * (K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ)) ^ (3 : ℕ) =
      A ^ (3 : ℕ) * (K.flow.connection t).scalarCurvature x ^ (-3 / 2 : ℝ) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (C.scalarCurvature_pos ht x).le]
    norm_num
  rw [heq, ← mul_assoc, ENNReal.ofReal_mul (mul_nonneg
    (RiemannianMetric.euclideanUnitBallVolume_nonneg 3) (pow_nonneg hA.le 3))] at hvol
  exact hvol

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
