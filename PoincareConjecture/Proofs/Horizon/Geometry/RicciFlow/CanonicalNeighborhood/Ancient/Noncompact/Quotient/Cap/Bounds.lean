import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Tube.Necks
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Bounds.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Bounds.Distance.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

noncomputable def twistedCapRadiusFactor (epsilon : ℝ) : ℝ :=
  6 * epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1) + 1

theorem twistedCapRadiusFactor_pos {epsilon : ℝ} (hε : 0 < epsilon) :
    0 < twistedCapRadiusFactor epsilon := by
  unfold twistedCapRadiusFactor
  positivity

noncomputable def twistedCapConstant
    (P : M26CanonicalNeighborhoodPredecessors.{u}) (epsilon : ℝ) : ℝ :=
  4 + twistedCapRadiusFactor epsilon +
    RiemannianMetric.euclideanUnitBallVolume 3 * twistedCapRadiusFactor epsilon ^ (3 : ℕ) +
      P.universal_noncollapsing.choose⁻¹

theorem twistedCapConstant_bounds (P : M26CanonicalNeighborhoodPredecessors.{u})
    {epsilon : ℝ} (hε : 0 < epsilon) :
    3 < twistedCapConstant P epsilon ∧
      twistedCapRadiusFactor epsilon < twistedCapConstant P epsilon ∧
      RiemannianMetric.euclideanUnitBallVolume 3 * twistedCapRadiusFactor epsilon ^ (3 : ℕ) <
        twistedCapConstant P epsilon ∧
      P.universal_noncollapsing.choose⁻¹ < twistedCapConstant P epsilon := by
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

theorem twistedCapConstant_pos (P : M26CanonicalNeighborhoodPredecessors.{u})
    {epsilon : ℝ} (hε : 0 < epsilon) : 0 < twistedCapConstant P epsilon :=
  (by norm_num : (0 : ℝ) < 3).trans (twistedCapConstant_bounds P hε).1

namespace M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem scalarRadius_eq_inv_sqrt (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    (K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ) =
      (Real.sqrt ((K.flow.connection t).scalarCurvature x))⁻¹ := by
  rw [neg_div, Real.rpow_neg (C.scalarCurvature_pos ht x).le, Real.sqrt_eq_rpow]

theorem neckSpacing_eq_scalarRadius (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (q : UnitTwoSphere) :
    C.neckSpacing (t := t) (epsilon := epsilon) q = epsilon⁻¹ *
      (K.flow.connection t).scalarCurvature (C.cover (q, 0)) ^ (-1 / 2 : ℝ) := by
  rw [C.scalarRadius_eq_inv_sqrt ht]
  rfl

theorem cap_intrinsicBound_lt_radiusFactor (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (q : UnitTwoSphere) :
    2 * (3 * C.neckSpacing (t := t) (epsilon := epsilon) q) +
      Real.sqrt 2 * (Real.pi + 1) /
        Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))) <
      twistedCapRadiusFactor epsilon *
        (K.flow.connection t).scalarCurvature (C.cover (q, 0)) ^ (-1 / 2 : ℝ) := by
  have hsqrt := Real.sqrt_pos.mpr (C.scalarCurvature_pos ht (C.cover (q, 0)))
  rw [C.scalarRadius_eq_inv_sqrt ht, ← div_eq_mul_inv]
  calc
    _ = (6 * epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1)) /
        Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))) := by
      dsimp [neckSpacing]
      ring
    _ < _ := div_lt_div_of_pos_right (by unfold twistedCapRadiusFactor; linarith) hsqrt

theorem capCarrier_subset_scalarRadius_ball (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (q : UnitTwoSphere) :
    interior (C.slabCore (3 * C.neckSpacing (t := t) (epsilon := epsilon) q)) ⊆
      (K.flow.metric t).ball (C.cover (q, 0)) (twistedCapRadiusFactor epsilon *
        (K.flow.connection t).scalarCurvature (C.cover (q, 0)) ^ (-1 / 2 : ℝ)) :=
  C.interior_slabCore_subset_ball ht q
    (mul_pos (by norm_num) (C.neckSpacing_pos ht hε q))
    (C.cap_intrinsicBound_lt_radiusFactor ht q)

theorem capCarrier_intrinsicDiameter_lt
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon D : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (q : UnitTwoSphere)
    (hD : twistedCapRadiusFactor epsilon < D) :
    intrinsicDiameter (K.flow.metric t)
      (interior (C.slabCore (3 * C.neckSpacing (t := t) (epsilon := epsilon) q))) <
      ENNReal.ofReal (D * scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
        (interior (C.slabCore (3 * C.neckSpacing (t := t) (epsilon := epsilon) q))) ^
          (-1 / 2 : ℝ)) := by
  rw [C.scalarCurvatureSupOn_eq ht
    (C.nonempty_interior_slabCore (mul_pos (by norm_num) (C.neckSpacing_pos ht hε q)))
    (C.cover (q, 0))]
  apply (C.intrinsicDiameter_interior_slabCore_le ht q _).trans_lt
  have hR := C.scalarRadius_pos ht (C.cover (q, 0))
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos
    ((twistedCapRadiusFactor_pos hε).trans hD) hR)).mpr
  exact (C.cap_intrinsicBound_lt_radiusFactor ht q).trans
    (mul_lt_mul_of_pos_right hD hR)

theorem capCarrier_volume_lt (C : M27TwistedSphereLineFlowCertificate K)
    (P : M26CanonicalNeighborhoodPredecessors.{u})
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
  apply (C.calibratedVolume_le_of_subset_scalarRadius_ball P ht (C.cover (q, 0))
    (twistedCapRadiusFactor_pos hε) (C.capCarrier_subset_scalarRadius_ball ht hε q)).trans_lt
  have hscale := Real.rpow_pos_of_pos (C.scalarCurvature_pos ht (C.cover (q, 0)))
    (-3 / 2 : ℝ)
  apply ENNReal.mul_lt_mul_left (ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
    ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos
    (RiemannianMetric.euclideanUnitBallVolume_pos 3)
    (pow_pos (twistedCapRadiusFactor_pos hε) 3)).trans hD)).mpr hD

theorem core_scalarRadius_ball_subset_capCarrier
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) {y : M}
    (hy : y ∈ interior (C.slabCore (C.neckSpacing (t := t) (epsilon := epsilon) q))) :
    closure ((K.flow.metric t).ball y
      ((K.flow.connection t).scalarCurvature y ^ (-1 / 2 : ℝ))) ⊆
      interior (C.slabCore (3 * C.neckSpacing (t := t) (epsilon := epsilon) q)) := by
  apply C.closure_ball_subset_interior_slabCore ht (C.scalarRadius_pos ht y).le
    (interior_subset hy)
  rw [C.scalarCurvature_eq ht y (C.cover (q, 0)), C.neckSpacing_eq_scalarRadius ht q]
  have hR := C.scalarRadius_pos ht (C.cover (q, 0))
  have hinv : 1 < epsilon⁻¹ := (one_lt_inv₀ hε).mpr (by linarith)
  nlinarith

end M27TwistedSphereLineFlowCertificate

end PoincareConjecture
