import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Fixed radius loss for the positive-history time window

The Old And Recent Histories section of
`reviews/contracts/2026-09-20-m47-complete-contract.md` applies the
Morgan--Tian Theorem 8.1 estimate at a fixed smaller tested radius. These
lemmas give that numerical choice and its exact cubic volume loss. They do
not assert the existence of a positive-age history or of its volume seed.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.Proofs.M47

/-- A fixed fraction of each tested radius fits half the positive history
age, as in the M47 complete-contract radius correction to Theorem 8.1. -/
noncomputable def seedRadiusFactor (epsilon age : ℝ) : ℝ :=
  min 1 (Real.sqrt (age / 2) / epsilon)

/-- The radius fraction is positive and never enlarges a ball; both inputs
are fixed old-data constants in the M47 complete-contract derivation. -/
theorem seedRadiusFactor_bounds {epsilon age : ℝ}
    (hepsilon : 0 < epsilon) (hage : 0 < age) :
    0 < seedRadiusFactor epsilon age ∧ seedRadiusFactor epsilon age ≤ 1 := by
  exact ⟨lt_min (by norm_num)
    (div_pos (Real.sqrt_pos.mpr (half_pos hage)) hepsilon), min_le_left _ _⟩

/-- Every tested radius up to epsilon has square smaller than the available
history age after the same fixed reduction; no flow-dependent age is chosen. -/
theorem seedRadiusFactor_sq_le {epsilon age r : ℝ}
    (hepsilon : 0 < epsilon) (hage : 0 < age) (hr : 0 < r) (hle : r ≤ epsilon) :
    (seedRadiusFactor epsilon age * r) ^ 2 ≤ age / 2 := by
  have htheta := seedRadiusFactor_bounds hepsilon hage
  have hscale : seedRadiusFactor epsilon age * epsilon ≤ Real.sqrt (age / 2) :=
    (le_div_iff₀ hepsilon).mp (min_le_right _ _)
  have hbound : seedRadiusFactor epsilon age * r ≤ Real.sqrt (age / 2) :=
    (mul_le_mul_of_nonneg_left hle htheta.1.le).trans hscale
  exact (pow_le_pow_left₀ (mul_nonneg htheta.1.le hr.le) hbound 2).trans_eq
    (Real.sq_sqrt (half_pos hage).le)

/-- The reduced time window has a strict spare half-age for Theorem 8.1,
as specified in the M47 complete-contract radius correction. -/
theorem seedRadiusFactor_sq_lt {epsilon age r : ℝ}
    (hepsilon : 0 < epsilon) (hage : 0 < age) (hr : 0 < r) (hle : r ≤ epsilon) :
    (seedRadiusFactor epsilon age * r) ^ 2 < age :=
  (seedRadiusFactor_sq_le hepsilon hage hr hle).trans_lt (half_lt_self hage)

/-- The exact coefficient lost on enlarging a reduced three-dimensional
ball is positive; this is the fixed theta-cubed loss in the M47 derivation. -/
theorem seedRadiusFactor_volume_constant_pos {epsilon age kappa : ℝ}
    (hepsilon : 0 < epsilon) (hage : 0 < age) (hkappa : 0 < kappa) :
    0 < kappa * seedRadiusFactor epsilon age ^ 3 :=
  mul_pos hkappa (pow_pos (seedRadiusFactor_bounds hepsilon hage).1 3)

/-- Inclusion of the reduced ball gives the exact cubic volume loss in the
M47 application of Theorem 8.1; no comparison curvature hypothesis is needed. -/
theorem volume_lower_of_reduced_ball
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (x : M) {theta r kappa : ℝ}
    (hr : 0 ≤ r) (htheta : theta ≤ 1)
    (hvolume : ENNReal.ofReal (kappa * (theta * r) ^ 3) ≤
      calibratedMetricVolume g (g.ball x (theta * r))) :
    ENNReal.ofReal ((kappa * theta ^ 3) * r ^ 3) ≤
      calibratedMetricVolume g (g.ball x r) := by
  rw [mul_pow, ← mul_assoc] at hvolume
  apply hvolume.trans
  apply measure_mono
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left hr htheta))

end PoincareMT.Proofs.M47
