import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.CalibratedBishopGromov
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapChapter11Geometry

/-!
# Exact Chapter 11 volume and Bishop-Gromov for cap-flow slices

The retained factor-one slice maps identify actual calibrated ball
volumes. The complete ordinary metric's Bishop-Gromov inequality thus
holds on the exact generalized slice, without changing its carrier.
Source: Morgan-Tian Theorem 12.29 and Claim 12.30, pp. 324-325.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.M34

variable {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F) (F := F.flow) R

include P

/-- Actual generalized ball volume is the original ordinary ball volume
at the projected center and the identical radius (Theorem 12.29). -/
theorem partialFlow_chapter11_ball_volume (p : (G).point) (r : ℝ) :
    calibratedMetricVolume ((G).metric p.1) (((G).metric p.1).ball p.2 r) =
      calibratedMetricVolume (F.flow.metric p.1)
        ((F.flow.metric p.1).ball (ordinaryChapter11Projection R p) r) := by
  let t : (partialFlowSpacetimeInterval F).domain :=
    ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  have h := ordinarySlice_ball_volume R.product t (partialFlow_chapter11_calculus F P R t)
    (ordinaryChapter11Projection R p) r
  change calibratedMetricVolume (R.product.slices (t : ℝ)).metricOnPoints
      ((R.product.slices (t : ℝ)).metricOnPoints.ball
        (R.product.sliceIdentification t p.2.val.2) r) = _ at h
  rw [ordinaryChapter11_identification_projection R t p.2] at h
  exact h

/-- The actual complete cap slice has nonincreasing positive-radius
calibrated ball ratios in its retained Chapter 11 realization. -/
theorem partialFlow_chapter11_bishopGromov (E0 : StandardCapEstimate g0) (p : (G).point) :
    AntitoneMetricBallVolumeRatio ((G).metric p.1) p.2 := by
  have hp := ordinaryChapter11Point_time_mem R p
  have hm := antitoneMetricBallVolumeRatio_of_complete_nonnegative_ricci
    (F.flow.metric p.1) (F.flow.connection p.1) (by norm_num)
    (partialFlow_complete F P.curvature hp)
    (fun x v => M04.nonneg_ricci_of_nonnegativeSectionalAt (F.flow.connection p.1) x
      (partialFlow_nonnegativeSectionalCurvature P.curvature E0 F p.1 hp x) v)
    (ordinaryChapter11Projection R p)
  intro r s hrs
  change calibratedMetricVolume ((G).metric p.1) (((G).metric p.1).ball p.2 s) /
      ENNReal.ofReal (s : ℝ) ^ 3 ≤
    calibratedMetricVolume ((G).metric p.1) (((G).metric p.1).ball p.2 r) /
      ENNReal.ofReal (r : ℝ) ^ 3
  rw [partialFlow_chapter11_ball_volume F P R p s, partialFlow_chapter11_ball_volume F P R p r]
  exact hm hrs

end PoincareMT.M34
