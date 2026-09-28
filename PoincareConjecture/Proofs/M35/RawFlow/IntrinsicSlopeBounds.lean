import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSlopeEquation
import PoincareConjecture.Proofs.M35.RawFlow.RawRadialVelocityBound
import PoincareConjecture.Proofs.M10.ScalarBound










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

theorem rawWarpingSlope_zero {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) :
    rawWarpingSlope P G hrotation t 0 = 1 := by
  unfold rawWarpingSlope
  rw [rawWarpingRadius_eq P G hrotation ht]
  exact (intrinsicWarpingRadius_hasDerivAt_zero (G.flow.metric t) (hrotation t ht)
    (G.complete P ht)).deriv

theorem rawWarpingSlope_bounds {t s : ℝ} (ht : t ∈ Ico 0 G.lifetime) (hs : 0 ≤ s) :
    rawWarpingSlope P G hrotation t s ∈ Icc 0 1 := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [rawWarpingSlope_zero P G hrotation ht]
    exact ⟨zero_le_one, le_rfl⟩
  have hr := rawInverseRadius_pos P G hrotation ht hs
  have hsec := raw_nonnegative_sectional P G ht
  change deriv (rawWarpingRadius P G hrotation t) s ∈ Icc 0 1
  rw [(rawWarpingRadius_hasDerivAt P G hrotation ht hs).deriv]
  exact ⟨axisWarpingSlope_nonneg (G.flow.connection t) (hrotation t ht) hsec (G.complete P ht) hr,
    axisWarpingSlope_le_one (G.flow.connection t) (hrotation t ht) hsec hr⟩

theorem rawWarpingSlope_deriv_nonpos {t s : ℝ} (ht : t ∈ Ico 0 G.lifetime) (hs : 0 < s) :
    deriv (rawWarpingSlope P G hrotation t) s ≤ 0 := by
  change deriv (deriv (rawWarpingRadius P G hrotation t)) s ≤ 0
  rw [(rawWarpingRadius_deriv_hasDerivAt P G hrotation ht hs).deriv]
  exact axisWarpingSecond_nonpos (G.flow.connection t) (hrotation t ht)
    (raw_nonnegative_sectional P G ht) (rawInverseRadius_pos P G hrotation ht hs)



theorem rawTangentialCurvature_bounds {T K : ℝ} (hK : 0 ≤ K)
    (hTlt : T < G.lifetime)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x, (G.flow.connection t).curvatureTensorNorm x ≤ K)
    {t s : ℝ} (ht : t ∈ Icc 0 T) (hs : 0 ≤ s) :
    rawTangentialCurvature P G hrotation t s ∈ Icc 0 (9 * K) := by
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  rcases hs.eq_or_lt with rfl | hs
  · have hf0 : rawWarpingRadius P G hrotation t 0 = 0 := by
      rw [rawWarpingRadius_eq P G hrotation htG]
      exact intrinsicWarpingRadius_zero (G.flow.metric t) (hrotation t htG) (G.complete P htG)
    simp only [rawTangentialCurvature, hf0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero,
      mem_Icc, le_refl, true_and]
    positivity
  have hp := rawWarpingSlope_bounds P G hrotation htG hs.le
  have hf : 0 < rawWarpingRadius P G hrotation t s := by
    rw [rawWarpingRadius_eq P G hrotation htG]
    exact intrinsicWarpingRadius_pos (G.flow.metric t) (hrotation t htG) (G.complete P htG) hs
  have hreaction : 0 ≤ rawTangentialCurvature P G hrotation t s := by
    apply div_nonneg _ (sq_nonneg _)
    nlinarith only [hp.1, hp.2]
  have hsecond := rawWarpingSlope_deriv_nonpos P G hrotation htG hs
  let x : StandardCapSpace := (radialArclengthOrderIso (G.flow.metric t) (hrotation t htG)
    (G.complete P htG)).symm s • EuclideanSpace.single (2 : Fin 3) 1
  have hscalar := M10.abs_scalarCurvature_le (G.flow.metric t) (G.flow.connection t) x
  norm_num at hscalar
  have hscalarBound : (G.flow.connection t).scalarCurvature x ≤ 9 * K := by
    have hcurv := hbound t ht x
    linarith [le_abs_self ((G.flow.connection t).scalarCurvature x)]
  have hformula := rotational_scalar_eq_intrinsicWarping (G.flow.metric t)
    (hrotation t htG) (G.complete P htG) (G.flow.connection t) hs
  rw [← rawWarpingRadius_eq P G hrotation htG] at hformula
  have hformula' : (G.flow.connection t).scalarCurvature x =
    2 * rawTangentialCurvature P G hrotation t s -
      4 * deriv (rawWarpingSlope P G hrotation t) s / rawWarpingRadius P G hrotation t s := by
    change (G.flow.connection t).scalarCurvature x =
      2 * ((1 - deriv (rawWarpingRadius P G hrotation t) s ^ 2) /
        rawWarpingRadius P G hrotation t s ^ 2) -
      4 * deriv (deriv (rawWarpingRadius P G hrotation t)) s / rawWarpingRadius P G hrotation t s
    rw [hformula]
    ring
  have hterm : 4 * deriv (rawWarpingSlope P G hrotation t) s /
      rawWarpingRadius P G hrotation t s ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hsecond) hf.le
  exact ⟨hreaction, by linarith⟩

end PoincareConjecture.M35.Uniqueness
