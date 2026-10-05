import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.WeakPhaseFlux
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Smooth radial boundary cutoffs and their scale invariant energy

The cutoff equals one on the half-radius disk and zero outside the full
radius disk. Its differential vanishes on both closed complementary
regions. Two-dimensional changes of scale preserve each column energy.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Function
open scoped ContDiff Topology

namespace PoincareMT

/-- The actual smooth transition applied to squared distance defines the radial boundary
cutoff. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis.
Project derivation: `proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
def m64BoundaryRadialCutoff (a : LoopPlane) (R : ℝ) (p : LoopPlane) : ℝ :=
  Real.smoothTransition ((4 / 3 : ℝ) * (1 - ‖R⁻¹ • (p - a)‖ ^ 2))

/-- The actual radial cutoff is smooth for every fixed radius. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_contDiff (a : LoopPlane) (R : ℝ) :
    ContDiff ℝ ∞ (m64BoundaryRadialCutoff a R) := by
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.mul (contDiff_const.sub
    ((contDiff_norm_sq ℝ).comp (by fun_prop :
      ContDiff ℝ ∞ (fun p : LoopPlane => R⁻¹ • (p - a)))))

/-- The actual radial cutoff is nonnegative. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_nonneg (a : LoopPlane) (R : ℝ) (p : LoopPlane) :
    0 ≤ m64BoundaryRadialCutoff a R p := Real.smoothTransition.nonneg _

/-- The actual radial cutoff is at most one. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_le_one (a : LoopPlane) (R : ℝ) (p : LoopPlane) :
    m64BoundaryRadialCutoff a R p ≤ 1 := Real.smoothTransition.le_one _

/-- For a positive radius the actual radial cutoff equals one on the inner half-radius ball.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. Project
derivation: `proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_eq_one {a p : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hp : ‖p - a‖ ≤ R / 2) : m64BoundaryRadialCutoff a R p = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hn : ‖R⁻¹ • (p - a)‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    nlinarith [mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hR.le),
      inv_mul_cancel₀ hR.ne']
  nlinarith [norm_nonneg (R⁻¹ • (p - a))]

/-- For a positive radius the actual radial cutoff is zero outside the outer ball. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_eq_zero {a p : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hp : R ≤ ‖p - a‖) : m64BoundaryRadialCutoff a R p = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hn : 1 ≤ ‖R⁻¹ • (p - a)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    nlinarith [mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hR.le),
      inv_mul_cancel₀ hR.ne']
  nlinarith

/-- The actual radial cutoff decreases as the distance from its center increases. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_antitone_radius {a p q : LoopPlane} {R : ℝ}
    (_hR : 0 < R) (hpq : ‖p - a‖ ≤ ‖q - a‖) :
    m64BoundaryRadialCutoff a R q ≤ m64BoundaryRadialCutoff a R p := by
  apply Real.smoothTransition.monotone
  have hn : ‖R⁻¹ • (p - a)‖ ≤ ‖R⁻¹ • (q - a)‖ := by
    simp only [norm_smul]
    exact mul_le_mul_of_nonneg_left hpq (norm_nonneg _)
  nlinarith [norm_nonneg (R⁻¹ • (p - a)), norm_nonneg (R⁻¹ • (q - a))]

/-- The actual radial cutoff derivative vanishes on both closed constant regions, including
their edges. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis.
Project derivation: `proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_fderiv_eq_zero {a p : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hp : ‖p - a‖ ≤ R / 2 ∨ R ≤ ‖p - a‖) :
    fderiv ℝ (m64BoundaryRadialCutoff a R) p = 0 := by
  rcases hp with hp | hp
  · apply IsLocalMax.fderiv_eq_zero
    exact Filter.Eventually.of_forall (fun q => by
      rw [m64BoundaryRadialCutoff_eq_one hR hp]
      exact m64BoundaryRadialCutoff_le_one a R q)
  · apply IsLocalMin.fderiv_eq_zero
    exact Filter.Eventually.of_forall (fun q => by
      rw [m64BoundaryRadialCutoff_eq_zero hR hp]
      exact m64BoundaryRadialCutoff_nonneg a R q)

/-- A positive-radius actual radial cutoff has compact support. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_hasCompactSupport (a : LoopPlane) {R : ℝ}
    (hR : 0 < R) : HasCompactSupport (m64BoundaryRadialCutoff a R) := by
  apply HasCompactSupport.intro (isCompact_closedBall a R)
  intro p hp
  apply m64BoundaryRadialCutoff_eq_zero hR
  exact le_of_lt (by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hp)

/-- The square of each actual radial cutoff derivative column is integrable. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_column_integrable (a : LoopPlane) {R : ℝ}
    (hR : 0 < R) (i : Fin 2) : Integrable (fun p =>
      (fderiv ℝ (m64BoundaryRadialCutoff a R) p (EuclideanSpace.single i 1)) ^ 2) := by
  have hc : Continuous (fun p =>
      fderiv ℝ (m64BoundaryRadialCutoff a R) p (EuclideanSpace.single i 1)) :=
    ((m64BoundaryRadialCutoff_contDiff a R).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hcompact := (m64BoundaryRadialCutoff_hasCompactSupport a hR).fderiv_apply
    (𝕜 := ℝ) (EuclideanSpace.single i 1)
  apply (hc.pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using (hcompact.mul_right (f' := fun p =>
    fderiv ℝ (m64BoundaryRadialCutoff a R) p (EuclideanSpace.single i 1)))

/-- The actual cutoff derivative column scales by the inverse positive radius. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_column_scaling (a p : LoopPlane) {R : ℝ}
    (_hR : 0 < R) (i : Fin 2) :
    fderiv ℝ (m64BoundaryRadialCutoff a R) p (EuclideanSpace.single i 1) =
      R⁻¹ * fderiv ℝ (m64BoundaryRadialCutoff 0 1) (R⁻¹ • (p - a))
        (EuclideanSpace.single i 1) := by
  have heq : m64BoundaryRadialCutoff a R =
      m64BoundaryRadialCutoff 0 1 ∘ (fun p : LoopPlane => R⁻¹ • (p - a)) := by
    ext p
    simp only [Function.comp_apply, m64BoundaryRadialCutoff, inv_one, sub_zero, one_smul]
  rw [heq]
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) p).sub_const a).const_smul (R⁻¹)
  change HasFDerivAt (fun p : LoopPlane => R⁻¹ • (p - a))
    (R⁻¹ • ContinuousLinearMap.id ℝ LoopPlane) p at hd
  rw [fderiv_comp p ((m64BoundaryRadialCutoff_contDiff 0 1).differentiable (by simp) _)
    hd.differentiableAt, ContinuousLinearMap.comp_apply, hd.fderiv]
  simp

/-- The planar change of variables cancels the derivative scaling and preserves the actual
cutoff column energy. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary
analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-boundary-energy-decay.md`. -/
theorem m64BoundaryRadialCutoff_column_energy (a : LoopPlane) {R : ℝ}
    (hR : 0 < R) (i : Fin 2) :
    (∫ p, (fderiv ℝ (m64BoundaryRadialCutoff a R) p
      (EuclideanSpace.single i 1)) ^ 2) =
      ∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p
        (EuclideanSpace.single i 1)) ^ 2 := by
  simp_rw [m64BoundaryRadialCutoff_column_scaling a _ hR i, mul_pow]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun q : LoopPlane =>
    (fderiv ℝ (m64BoundaryRadialCutoff 0 1) (R⁻¹ • q)
      (EuclideanSpace.single i 1)) ^ 2) a]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun p : LoopPlane =>
    (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p (EuclideanSpace.single i 1)) ^ 2) hR.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, inv_pow]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hR.ne'), one_mul]

end PoincareMT
