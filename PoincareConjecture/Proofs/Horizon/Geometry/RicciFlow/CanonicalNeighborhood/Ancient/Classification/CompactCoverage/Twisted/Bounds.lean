import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Twisted.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.TwistedBuffered.Bounds










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientKappaCapServices

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution 3 M}

theorem bufferedCarrier_volume_lt (P : AncientKappaCapServices.{u})
    (C : M27TwistedSphereLineFlowCertificate K)
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
  apply (P.calibratedVolume_le_of_subset_scalarRadius_ball C ht (C.cover (q, 0))
    (twistedCapRadiusFactor_pos (half_pos hε)) hball).trans_lt
  have hscale := Real.rpow_pos_of_pos (C.scalarCurvature_pos ht (C.cover (q, 0)))
    (-3 / 2 : ℝ)
  apply ENNReal.mul_lt_mul_left (ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
    ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos
    (RiemannianMetric.euclideanUnitBallVolume_pos 3)
    (pow_pos (twistedCapRadiusFactor_pos (half_pos hε)) 3)).trans hD)).mpr hD

end PoincareConjecture.AncientKappaCapServices
