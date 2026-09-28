import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Twisted.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientKappaCapServices

noncomputable def twistedCapConstant (P : AncientKappaCapServices.{u}) (epsilon : ℝ) : ℝ :=
  4 + twistedCapRadiusFactor epsilon +
    RiemannianMetric.euclideanUnitBallVolume 3 * twistedCapRadiusFactor epsilon ^ (3 : ℕ) +
      P.universal_noncollapsing.choose⁻¹

theorem twistedCapConstant_bounds (P : AncientKappaCapServices.{u})
    {epsilon : ℝ} (hε : 0 < epsilon) :
    3 < P.twistedCapConstant epsilon ∧
      twistedCapRadiusFactor epsilon < P.twistedCapConstant epsilon ∧
      RiemannianMetric.euclideanUnitBallVolume 3 * twistedCapRadiusFactor epsilon ^ (3 : ℕ) <
        P.twistedCapConstant epsilon ∧
      P.universal_noncollapsing.choose⁻¹ < P.twistedCapConstant epsilon := by
  have hA := twistedCapRadiusFactor_pos hε
  have hω := RiemannianMetric.euclideanUnitBallVolume_pos 3
  have hκ := inv_pos.mpr P.universal_noncollapsing.choose_spec.1
  have hV := mul_pos hω (pow_pos hA 3)
  unfold twistedCapConstant
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem twistedCapConstant_pos (P : AncientKappaCapServices.{u})
    {epsilon : ℝ} (hε : 0 < epsilon) : 0 < P.twistedCapConstant epsilon :=
  (by norm_num : (0 : ℝ) < 3).trans (P.twistedCapConstant_bounds hε).1

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem scalarEvolution_bound (P : AncientKappaCapServices.{u})
    (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    |(K.flow.connection t).laplacian (K.flow.connection t).scalarCurvature x +
      2 * (K.flow.connection t).ricciNormSq x| ≤
        2 * (K.flow.connection t).scalarCurvature x ^ 2 := by
  have hD := P.tensor_calculus M (K.flow.metric t) (K.flow.connection t)
  have hRic : ∀ v : TangentSpace (𝓡 3) x,
      0 ≤ (K.flow.connection t).ricci x v v := fun v =>
    ((K.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator hD x
      (K.nonnegative_curvature_operator t ht x) v).1
  have hnorm :=
    (K.flow.connection t).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg hD x hRic
  have hnorm0 : 0 ≤ (K.flow.connection t).ricciNormSq x :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [C.scalarLaplacian_eq_zero ht x, zero_add,
    abs_of_nonneg (mul_nonneg (by norm_num) hnorm0)]
  linarith

theorem scalarRadius_volume_lower_bound_of_noncollapsed (P : AncientKappaCapServices.{u})
    (C : M27TwistedSphereLineFlowCertificate K)
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

theorem calibratedVolume_le_of_subset_ball (P : AncientKappaCapServices.{u})
    {t : ℝ} (ht : t ≤ 0) (x : M) {r : ℝ} (hr : 0 < r)
    {U : Set M} (hU : U ⊆ (K.flow.metric t).ball x r) :
    calibratedMetricVolume (K.flow.metric t) U ≤
      ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 3 * r ^ (3 : ℕ)) := by
  have hRic (y : M) (v : TangentSpace (𝓡 3) y) :
      0 ≤ (K.flow.connection t).ricci y v v :=
    ((K.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (P.tensor_calculus M (K.flow.metric t) (K.flow.connection t)) y
      (K.nonnegative_curvature_operator t ht y) v).1
  have hupper := (K.flow.metric t).ball_volume_div_pow_le_euclideanUnitBallVolume
    (K.flow.connection t) (by norm_num) (K.complete t ht) hRic x hr
  apply (MeasureTheory.measure_mono hU).trans
  rw [calibratedMetricVolume_eq_volumeMeasure,
    ← ENNReal.ofReal_toReal ((K.flow.metric t).ball_volume_ne_top_of_metricComplete
      (K.complete t ht) x r)]
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (pow_pos hr 3)).mp hupper)

theorem calibratedVolume_le_of_subset_scalarRadius_ball (P : AncientKappaCapServices.{u})
    (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) {A : ℝ} (hA : 0 < A)
    {U : Set M} (hU : U ⊆ (K.flow.metric t).ball x
      (A * (K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))) :
    calibratedMetricVolume (K.flow.metric t) U ≤
      ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume 3 * A ^ (3 : ℕ)) *
        ENNReal.ofReal ((K.flow.connection t).scalarCurvature x ^ (-3 / 2 : ℝ)) := by
  have hvol := P.calibratedVolume_le_of_subset_ball ht x
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

theorem capCarrier_volume_lt (P : AncientKappaCapServices.{u})
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon D : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (q : UnitTwoSphere)
    (hD : RiemannianMetric.euclideanUnitBallVolume 3 *
      twistedCapRadiusFactor epsilon ^ (3 : ℕ) < D) :
    calibratedMetricVolume (K.flow.metric t)
      (interior (C.slabCore (3 * C.neckSpacing (t := t) (epsilon := epsilon) q))) <
      ENNReal.ofReal D * ENNReal.ofReal
        (scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
          (interior (C.slabCore (3 * C.neckSpacing (t := t) (epsilon := epsilon) q))) ^
            (-3 / 2 : ℝ)) := by
  rw [C.scalarCurvatureSupOn_eq ht
    (C.nonempty_interior_slabCore (mul_pos (by norm_num) (C.neckSpacing_pos ht hε q)))
    (C.cover (q, 0))]
  apply (P.calibratedVolume_le_of_subset_scalarRadius_ball C ht (C.cover (q, 0))
    (twistedCapRadiusFactor_pos hε) (C.capCarrier_subset_scalarRadius_ball ht hε q)).trans_lt
  have hscale := Real.rpow_pos_of_pos (C.scalarCurvature_pos ht (C.cover (q, 0)))
    (-3 / 2 : ℝ)
  apply ENNReal.mul_lt_mul_left (ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
    ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos
    (RiemannianMetric.euclideanUnitBallVolume_pos 3)
    (pow_pos (twistedCapRadiusFactor_pos hε) 3)).trans hD)).mpr hD

end PoincareConjecture.AncientKappaCapServices
