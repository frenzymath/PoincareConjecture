import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.IntrinsicCurvatureJetsBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.IntrinsicPolynomialDecay
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RadialGauge.PolynomialJetDecay

/-!
# Rapid decay of the actual intrinsic warping jets

Morgan-Tian Section 12.6, pp. 309-320, with the corrected radial gauge.
The actual polynomial slope estimate and retained curvature derivative
bounds imply every polynomial decay order for every positive-order
warping derivative on the original closed slab. This supplies the
quantitative target jets needed at arbitrary restart times.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M35.Uniqueness

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

include H

/-- Every actual radial derivative of the slope decays faster than each
fixed reciprocal polynomial, uniformly on a single closed raw slab. -/
theorem raw_intrinsic_slope_jets_polynomial_decay {T : ℝ} (hT : 0 < T)
    (hTlt : T < G.lifetime) :
    ∀ j N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 0,
      (1 + r ^ 2) ^ N * |iteratedDeriv j (rawWarpingSlope P G hrotation t) r| ≤ C := by
  let A := ↥(Icc (0 : ℝ) T)
  have ht (a : A) : a.1 ∈ Ico 0 G.lifetime := ⟨a.2.1, a.2.2.trans_lt hTlt⟩
  have hs (a : A) : ContDiff ℝ ∞ (rawWarpingSlope P G hrotation a.1) :=
    rawWarpingSlope_contDiff P G hrotation (ht a)
  have hjets (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : A) r, 0 ≤ r →
      |iteratedDeriv j (rawWarpingSlope P G hrotation a.1) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ :=
      raw_intrinsic_warping_jets_bounded_on_slab P H G hT hTlt hrotation (j + 1)
    refine ⟨C, hC.le, ?_⟩
    intro a r hr
    change |iteratedDeriv j (deriv (rawWarpingRadius P G hrotation a.1)) r| ≤ C
    rw [← iteratedDeriv_succ', rawWarpingRadius_eq P G hrotation (ht a)]
    exact hCb a.1 a.2 r hr
  have hvalue (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : A) r, 0 ≤ r →
      (1 + r ^ 2) ^ N * |rawWarpingSlope P G hrotation a.1 r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ := raw_intrinsic_slope_polynomial_decay P H G hrotation hT hTlt N
    refine ⟨C, hC.le, ?_⟩
    intro a r hr
    rw [abs_of_nonneg (rawWarpingSlope_bounds P G hrotation (ht a) hr).1]
    exact hCb a.1 a.2 r hr
  intro j N
  obtain ⟨C, hC, hCb⟩ := RadialGauge.polynomial_iteratedDeriv_bounds hs hjets hvalue j N
  refine ⟨C + 1, by positivity, ?_⟩
  intro t ht r hr
  exact (hCb ⟨t, ht⟩ r hr).trans (by linarith)

/-- The same closed-slab estimate applies directly to every actual
positive-order intrinsic warping derivative. -/
theorem raw_intrinsic_warping_jets_polynomial_decay {T : ℝ} (hT : 0 < T)
    (hTlt : T < G.lifetime) :
    ∀ j N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 0,
      (1 + r ^ 2) ^ N * |iteratedDeriv (j + 1) (rawWarpingRadius P G hrotation t) r| ≤ C := by
  intro j N
  obtain ⟨C, hC, hCb⟩ :=
    raw_intrinsic_slope_jets_polynomial_decay P H G hrotation hT hTlt j N
  refine ⟨C, hC, ?_⟩
  intro t ht r hr
  rw [iteratedDeriv_succ']
  exact hCb t ht r hr

end PoincareMT.M35.Uniqueness
