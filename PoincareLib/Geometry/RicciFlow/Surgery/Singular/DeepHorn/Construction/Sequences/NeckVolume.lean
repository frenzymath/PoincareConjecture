import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.NeckVolumeSmallBalls
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Neck.ScalarControl
import PoincareLib.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Volume.Calibration
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
open scoped PoincareMT.DeepHornSource

/-!
# Strong-neck noncollapse and normalized terminal volume

Morgan--Tian Claim 11.32, printed pp. 287-288, supplies noncollapse from
actual centered strong necks. The curvature test forces the radius into
the range of the spatial cubic volume estimate. At the neck scale the
same estimate supplies M30's exact terminal-volume field with radius one.

Re-derived from the read-only DeepHorn `Neck/Volume.lean` declarations
`GeneralizedStrongNeck.scale_eq_inv_sqrt_scalar`,
`GeneralizedStrongNeck.calibratedVolume_center_ball_lower`, and
`GeneralizedBlowupSequence.terminal_volume_of_strongNecks`, and from
`Neck/Volume/SmallBalls.lean` declarations
`GeneralizedStrongNeck.radius_le_two_scale_of_curvature_bound` and
`GeneralizedStrongNeck.noncollapsed_at_center`. The normalized-volume
argument uses the small-ball estimate at the neck scale, the owned scalar
normalization, and the actual lower M15 calibration theorem.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}

private theorem strongNeck_scale_eq_inv_sqrt_scalar (N : GeneralizedStrongNeck F t epsilon) :
    N.scale = (Real.sqrt (F.scalar ⟨t, N.center⟩))⁻¹ := by
  rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, Real.sqrt_eq_rpow]
  rfl

/-- The actual parabolic curvature test bounds the radius by twice the
strong-neck scale, as used in Claim 11.32, printed p. 288. -/
theorem strongNeck_radius_le_two_scale_of_curvature_bound
    (N : GeneralizedStrongNeck F t epsilon) (hepsilon : epsilon < 1 / 2)
    {r : ℝ} (hr : 0 < r)
    (hcurv : |F.curvatureNorm ⟨t, N.center⟩| ≤ r⁻¹ ^ 2) :
    r ≤ 2 * N.scale := by
  have hscalar := (F.connection t).scalarCurvature_le_curvatureTensorNorm_sharp N.center
  have hR : (F.connection t).scalarCurvature N.center ≤ 3 * r⁻¹ ^ 2 := by
    exact hscalar.trans (by
      norm_num only [Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcurv) (by norm_num))
  have hnorm := neckScale_sq_mul_scalar_center (spatialNeck N hepsilon)
  change N.scale ^ 2 * (F.connection t).scalarCurvature N.center = 1 at hnorm
  have hm := mul_le_mul_of_nonneg_left hR (sq_nonneg r)
  have hcancel : r ^ 2 * (3 * r⁻¹ ^ 2) = 3 := by field_simp [hr.ne']
  rw [hcancel] at hm
  have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg N.scale)
  have hprod : N.scale ^ 2 * (r ^ 2 * (F.connection t).scalarCurvature N.center) = r ^ 2 := by
    calc
      _ = r ^ 2 * (N.scale ^ 2 * (F.connection t).scalarCurvature N.center) := by ring
      _ = r ^ 2 := by rw [hnorm, mul_one]
  rw [hprod] at hm'
  nlinarith [N.scale_pos]

/-- Strong-neck centers have one common noncollapse constant for every
allowed scale in the actual cylinder test; Claim 11.32, printed p. 288. -/
theorem strongNeck_noncollapsed_at_center (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) (r₀ : ℝ) :
    GeneralizedKappaNoncollapsedAt F ⟨t, N.center⟩ neckNoncollapseConstant r₀ := by
  intro r hr _ _ e hidentity hcurv
  have hzero : (0 : ℝ) ∈ Ioc (-r ^ 2) 0 := ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩
  have hcenter : N.center ∈ (F.metric t).ball N.center r := by
    change (F.metric t).edist N.center N.center < ENNReal.ofReal r
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hr
  have htop := hcurv 0 hzero N.center hcenter
  rw [hidentity hzero N.center hcenter] at htop
  have hrscale := strongNeck_radius_le_two_scale_of_curvature_bound N hepsilon hr htop
  have hv := neck_volume_center_ball_lower_of_le_two_scale (spatialNeck N hepsilon) hr hrscale
  rw [PoincareMT.Proofs.M15.calibratedMetricVolume_eq_euclideanHausdorff]
  exact hv

/-- A radius-one scalar-normalized ball has fixed positive actual calibrated
volume, supplying the terminal-volume input of Claim 11.32, pp. 287-288. -/
theorem strongNeck_calibratedVolume_center_ball_lower
    (N : GeneralizedStrongNeck F t epsilon) (hepsilon : epsilon < 1 / 2) :
    ENNReal.ofReal (neckNoncollapseConstant /
        (Real.sqrt (F.scalar ⟨t, N.center⟩)) ^ 3) ≤
      calibratedMetricVolume (F.metric t)
        ((F.metric t).ball N.center (1 / Real.sqrt (F.scalar ⟨t, N.center⟩))) := by
  have hv := neck_volume_center_ball_lower_of_le_two_scale
    (spatialNeck N hepsilon) N.scale_pos
    (show N.scale ≤ 2 * N.scale by linarith [N.scale_pos])
  change ENNReal.ofReal (neckNoncollapseConstant * N.scale ^ 3) ≤
    (F.metric t).volumeMeasure ((F.metric t).ball N.center N.scale) at hv
  rw [strongNeck_scale_eq_inv_sqrt_scalar, inv_pow, ← div_eq_mul_inv] at hv
  rw [PoincareMT.Proofs.M15.calibratedMetricVolume_eq_euclideanHausdorff, one_div]
  exact hv

/-- Eventual centered strong necks give the exact M30 terminal-volume field
used in Claim 11.32, printed pp. 287-288, with common radius one. -/
theorem terminal_volume_of_strongNecks (S : GeneralizedBlowupSequence.{u})
    (hneck : ∀ᶠ k : ℕ in Filter.atTop,
      ∃ epsilon : ℝ, epsilon < 1 / 2 ∧
        ∃ N : GeneralizedStrongNeck (S.flow k) (S.base k).1 epsilon,
          N.center = (S.base k).2) :
    ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k : ℕ in Filter.atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1) (S.baseBall k rho) := by
  refine ⟨1, neckNoncollapseConstant, zero_lt_one, neckNoncollapseConstant_pos, ?_⟩
  filter_upwards [hneck] with k hk
  obtain ⟨epsilon, hepsilon, N, hcenter⟩ := hk
  simpa only [GeneralizedBlowupSequence.baseBall, GeneralizedBlowupSequence.scale,
    hcenter, Sigma.eta] using strongNeck_calibratedVolume_center_ball_lower N hepsilon

end PoincareMT.M32
