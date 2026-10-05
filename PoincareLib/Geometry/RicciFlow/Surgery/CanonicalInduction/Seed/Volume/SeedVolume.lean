import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Volume
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.RoundPositive
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Volume.NeckVolume
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Volume.CapVolume
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.TestScalar

/-!
# Canonical volume seeds at a scalar crossing

Morgan--Tian Proposition 16.3 and Remark 16.2, p. 368, with Definition
9.72, pp. 230-231. The historical cap-contact argument in
`reviews/contracts/2026-09-20-m47-complete-contract.md` uses these estimates
at a fixed scalar crossing in a nonpositive component. This module reuses
the proved M46 neck and cap volume estimates. It does not construct the
crossing, the surviving search region or the overlapping-ball chain.
-/

set_option autoImplicit false

open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT

/-- The M46 services used in Proposition 16.3, p. 368, are identical fields
of the M47 predecessor record; no additional predecessor is required. -/
theorem M47Predecessors.toM46 (P : M47Predecessors.{u}) : M46Predecessors.{u} :=
  { m04 := P.m04
    m11 := P.m11
    m12 := P.m12
    m13 := P.m13
    m14 := P.m14
    m15 := P.m15
    regular_history := P.regular_history }

namespace Proofs.M47

/-- The common neck/cap volume density depends only on the canonical
constant, as in Proposition 16.3, p. 368. -/
noncomputable def canonicalSeedDensity (C : ℝ) : ℝ :=
  min M46.canonicalNeckVolumeFloor (M46.canonicalCapVolumeFloor (max 1 C))

/-- Both canonical alternatives have positive density, Proposition 16.3,
p. 368. The maximum with one keeps the cap coefficient meaningful. -/
theorem canonicalSeedDensity_pos (C : ℝ) : 0 < canonicalSeedDensity C :=
  lt_min M46.canonicalNeckVolumeFloor_pos
    (M46.canonicalCapVolumeFloor_pos (le_max_left _ _))

/-- A nonpositive canonical point has a volume seed whenever its scalar
fits the tested radius. This is the pointwise content of Proposition 16.3,
p. 368, and introduces no historical cutoff or time-cylinder premise. -/
theorem canonical_seed_volume (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {t rho s : ℝ} {x : (F.slice t).carrier}
    (hcanonical : SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 200)
    (hhigh : rho⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x)
    (hpinch : SurgeryPinchedAt (F.connection t) t)
    (hs : 0 < s) (hscalar : (F.connection t).scalarCurvature x ≤ 9 * s⁻¹ ^ 2) :
    ENNReal.ofReal (canonicalSeedDensity F.parameters.C * s ^ 3) ≤
      calibratedMetricVolume (F.metric t) ((F.metric t).ball x s) := by
  rcases M46.canonical_neck_or_cap_of_not_positive hcanonical hpositive with
    ⟨N, hx⟩ | ⟨N, _, hC, hconnection, hx⟩
  · have hNscalar : N.neck.connection.scalarCurvature N.neck.center ≤ 9 * s⁻¹ ^ 2 := by
      rw [N.connection_eq, hx]
      exact hscalar
    have hscale := M46.canonicalNeck_scale_of_scalar_bound N.neck hs hNscalar
    have hvolume := M46.canonicalNeck_test_ball_volume N.neck hs hscale
    rw [hx] at hvolume
    rw [M15.calibratedMetricVolume_eq_volumeMeasure]
    apply (ENNReal.ofReal_le_ofReal ?_).trans hvolume
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hs.le 3)
  · have hNhigh : rho⁻¹ ^ 2 ≤ N.connection.scalarCurvature x := by
      rw [hconnection]
      exact hhigh
    have hsmall : N.core_radius x ≤ 1 / 200 :=
      (M46.canonicalCap_core_radius_le N hx hrho hNhigh).trans hrhoSmall
    have hNpinch : SurgeryPinchedAt N.connection t := by
      rw [hconnection]
      exact hpinch
    have hNscalar : N.connection.scalarCurvature x ≤ 9 * s⁻¹ ^ 2 := by
      rw [hconnection]
      exact hscalar
    have hvolume := M46.canonicalCap_test_ball_volume P.toM46 N hx
      (le_max_left 1 F.parameters.C) (hC.trans (le_max_right _ _)) hs
      hNpinch hsmall hNscalar
    apply (ENNReal.ofReal_le_ofReal ?_).trans hvolume
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hs.le 3)

/-- At a fixed high scalar level, the reciprocal square-root radius
automatically meets the volume test. This supplies the crossing seed in the
Uniform Seed section of the September 20 M47 complete-contract derivation. -/
theorem canonical_crossing_seed_volume (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {t rho H : ℝ} {x : (F.slice t).carrier}
    (hcanonical : SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 200)
    (hlevel : rho⁻¹ ^ 2 ≤ H) (hscalar : (F.connection t).scalarCurvature x = H)
    (hpinch : SurgeryPinchedAt (F.connection t) t) :
    0 < (Real.sqrt H)⁻¹ ∧
      ENNReal.ofReal (canonicalSeedDensity F.parameters.C * (Real.sqrt H)⁻¹ ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball x (Real.sqrt H)⁻¹) := by
  have hH : 0 < H := (pow_pos (inv_pos.mpr hrho) 2).trans_le hlevel
  have hs : 0 < (Real.sqrt H)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hH)
  refine ⟨hs, canonical_seed_volume P hcanonical hpositive hrho hrhoSmall ?_ hpinch hs ?_⟩
  · simpa only [hscalar] using hlevel
  · rw [hscalar, inv_inv, Real.sq_sqrt hH.le]
    linarith

end Proofs.M47

end PoincareMT
