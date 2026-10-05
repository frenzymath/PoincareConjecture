import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Estimates.LateVolume
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Estimates.EarlyVolume

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Thm8_10_Assembly.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# The compact noncollapsing theorem

Morgan-Tian Theorem 8.10, pp. 176-177. The positive minimum of the
early and late constants is uniform before all geometric inputs.
Restriction to the tested component covers disconnected manifolds.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-21-compact-assembly.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.Generalized.Noncollapse

/-- Compact Theorem 8.10, pp. 176-177, with constants depending only
on the initial unit-ball volume bound and the maximum flow time. -/
theorem compactTheorem810
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    (hOrdinary : M14OrdinaryProviders.{u} 3) :
    M15CompactTheorem810.{u} := by
  intro omega T0 homega hT0
  obtain ⟨ke, hke, hearly⟩ := exists_compact_initial_volume_bound 3 (by decide) omega homega
  obtain ⟨kl, hkl, hlate⟩ := exists_compact_late_volume_bound hM04 hM12 hM13 hM14
    hOrdinary omega T0 homega hT0
  refine ⟨{
    omega_pos := homega
    T₀_pos := hT0
    kappa := min ke kl
    kappa_pos := lt_min hke hkl
    estimate := ?_
  }⟩
  apply compact_estimate_of_connected
  intro M _ _ _ _ _ _ _ _ _ T F D
  by_cases hl : 1 / (32 * (3 : ℝ) ^ 6) ≤ D.t₀
  · apply le_trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_right ke kl) (pow_nonneg D.radius_pos.le 3)))
    exact hlate M T F D hl
  · have ht : D.t₀ ∈ Icc 0 (min T (1 / (32 * (3 : ℝ) ^ 6))) :=
      ⟨D.t₀_nonneg, le_min D.t₀_le_T (le_of_lt (lt_of_not_ge hl))⟩
    have hr1 : D.r ≤ 1 := by
      have hdelta : 1 / (32 * (3 : ℝ) ^ 6) ≤ 1 := by norm_num
      have htr : D.t₀ ≤ 1 := (le_of_lt (lt_of_not_ge hl)).trans hdelta
      nlinarith [D.radius_sq_le_t₀]
    have hinit (q : M) : (F.connection 0).curvatureTensorNorm q ≤ 1 :=
      (le_abs_self _).trans (D.initial_curvature_bound q)
    apply le_trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_left ke kl) (pow_nonneg D.radius_pos.le 3)))
    exact hearly M T D.T_pos F hinit D.initial_unit_ball_volume D.t₀ ht
      D.p D.r D.radius_pos hr1

end PoincareMT.Generalized.Noncollapse
