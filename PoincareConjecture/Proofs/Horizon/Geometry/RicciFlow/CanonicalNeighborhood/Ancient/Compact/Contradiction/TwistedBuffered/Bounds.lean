import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Cap.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.TwistedBuffered.Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution 3 M}

theorem neckSpacing_half (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (q : UnitTwoSphere) :
    C.neckSpacing (t := t) (epsilon := epsilon / 2) q =
      2 * C.neckSpacing (t := t) (epsilon := epsilon) q := by
  dsimp [neckSpacing]
  rw [inv_div]
  ring

theorem buffered_intrinsicBound_lt_radiusFactor
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (q : UnitTwoSphere) :
    2 * (4 * C.neckSpacing (t := t) (epsilon := epsilon) q) +
      Real.sqrt 2 * (Real.pi + 1) /
        Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))) <
      twistedCapRadiusFactor (epsilon / 2) *
        (K.flow.connection t).scalarCurvature (C.cover (q, 0)) ^ (-1 / 2 : ℝ) := by
  have hsqrt := Real.sqrt_pos.mpr (C.scalarCurvature_pos ht (C.cover (q, 0)))
  rw [C.scalarRadius_eq_inv_sqrt ht, ← div_eq_mul_inv]
  calc
    _ = (8 * epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1)) /
        Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))) := by
      dsimp [neckSpacing]
      ring
    _ < _ := div_lt_div_of_pos_right (by
      unfold twistedCapRadiusFactor
      simp only [mul_inv_rev, inv_inv, div_eq_mul_inv]
      nlinarith [inv_pos.mpr hε]) hsqrt

theorem bufferedCarrier_intrinsicDiameter_lt
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon D : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (q : UnitTwoSphere)
    (hD : twistedCapRadiusFactor (epsilon / 2) < D) :
    intrinsicDiameter (K.flow.metric t)
      (interior (C.slabCore (4 * C.neckSpacing (t := t) (epsilon := epsilon) q))) <
      ENNReal.ofReal (D * scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
        (interior (C.slabCore (4 * C.neckSpacing (t := t) (epsilon := epsilon) q))) ^
          (-1 / 2 : ℝ)) := by
  rw [C.scalarCurvatureSupOn_eq ht
    (C.nonempty_interior_slabCore (mul_pos (by norm_num) (C.neckSpacing_pos ht hε q)))
    (C.cover (q, 0))]
  apply (C.intrinsicDiameter_interior_slabCore_le ht q _).trans_lt
  have hR := C.scalarRadius_pos ht (C.cover (q, 0))
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos
    ((twistedCapRadiusFactor_pos (half_pos hε)).trans hD) hR)).mpr
  exact (C.buffered_intrinsicBound_lt_radiusFactor ht hε q).trans
    (mul_lt_mul_of_pos_right hD hR)

theorem bufferedCarrier_volume_lt (C : M27TwistedSphereLineFlowCertificate K)
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {t epsilon D : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (q : UnitTwoSphere)
    (hD : RiemannianMetric.euclideanUnitBallVolume 3 *
      twistedCapRadiusFactor (epsilon / 2) ^ (3 : ℕ) < D) :
    calibratedMetricVolume (K.flow.metric t)
      (interior (C.slabCore (4 * C.neckSpacing (t := t) (epsilon := epsilon) q))) <
      ENNReal.ofReal D * ENNReal.ofReal
        (scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
          (interior (C.slabCore (4 * C.neckSpacing (t := t) (epsilon := epsilon) q))) ^
            (-3 / 2 : ℝ)) := by
  rw [C.scalarCurvatureSupOn_eq ht
    (C.nonempty_interior_slabCore (mul_pos (by norm_num) (C.neckSpacing_pos ht hε q)))
    (C.cover (q, 0))]
  have hball := C.interior_slabCore_subset_ball ht q
    (mul_pos (by norm_num) (C.neckSpacing_pos ht hε q))
    (C.buffered_intrinsicBound_lt_radiusFactor ht hε q)
  apply (C.calibratedVolume_le_of_subset_scalarRadius_ball P ht (C.cover (q, 0))
    (twistedCapRadiusFactor_pos (half_pos hε)) hball).trans_lt
  have hscale := Real.rpow_pos_of_pos (C.scalarCurvature_pos ht (C.cover (q, 0)))
    (-3 / 2 : ℝ)
  apply ENNReal.mul_lt_mul_left (ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
    ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos
    (RiemannianMetric.euclideanUnitBallVolume_pos 3)
    (pow_pos (twistedCapRadiusFactor_pos (half_pos hε)) 3)).trans hD)).mpr hD

theorem buffered_core_scalarRadius_ball_subset_carrier
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) {y : M}
    (hy : y ∈ interior (C.slabCore
      (2 * C.neckSpacing (t := t) (epsilon := epsilon) q))) :
    closure ((K.flow.metric t).ball y
      ((K.flow.connection t).scalarCurvature y ^ (-1 / 2 : ℝ))) ⊆
      interior (C.slabCore (4 * C.neckSpacing (t := t) (epsilon := epsilon) q)) := by
  apply C.closure_ball_subset_interior_slabCore ht (C.scalarRadius_pos ht y).le
    (interior_subset hy)
  rw [C.scalarCurvature_eq ht y (C.cover (q, 0)), C.neckSpacing_eq_scalarRadius ht q]
  have hR := C.scalarRadius_pos ht (C.cover (q, 0))
  have hinv : 1 < epsilon⁻¹ := (one_lt_inv₀ hε).mpr (by linarith)
  nlinarith

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
