import PoincareLib.Geometry.CurveShortening.Evolution.Flow
import Mathlib.Tactic.FieldSimp

/-!
# Positive speed and the normalized spatial tangent

The pointwise metric facts used in Morgan--Tian Lemma 19.6, pp. 441-442,
and in the 2015 correction, Lemma 0.1, p. 3. These identities retain the
actual metric and parameter velocity, including at endpoint slices.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

/-- Speed is nonnegative without immersion; MT2007 Lemma 19.6, p. 441. -/
theorem speed_nonneg (t x : ℝ) : 0 ≤ curveSpeed F c t x :=
  Real.sqrt_nonneg _

/-- The speed square is the actual velocity self-pairing; MT2007 p. 441. -/
theorem speed_sq (t x : ℝ) :
    curveSpeed F c t x ^ 2 =
      (F.metric t).inner (c x t) (curveVelocity (fun y ↦ c y t) x)
        (curveVelocity (fun y ↦ c y t) x) := by
  apply Real.sq_sqrt
  exact ((F.metric t).toRiemannianMetric.toCore (c x t)).re_inner_nonneg _

/-- Immersion gives positive speed, including at endpoints; correction Lemma 0.1, p. 3. -/
theorem speed_pos (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Set.Icc a b)
    (x : ℝ) : 0 < curveSpeed F c t x := by
  exact Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hc.immersed t ht x))

/-- The normalized parameter velocity is a unit vector; MT2007 Lemma 19.6, p. 441. -/
theorem unitTangent_inner_self (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) (x : ℝ) :
    (F.metric t).inner (c x t) (spatialUnitTangent F c t x)
      (spatialUnitTangent F c t x) = 1 := by
  have hv := (speed_pos F c hc ht x).ne'
  simp only [spatialUnitTangent, map_smul, smul_apply, smul_eq_mul]
  rw [← speed_sq F c t x]
  field_simp

/-- The tangent norm uses the chosen flow metric; MT2007 Lemma 19.6, p. 441. -/
theorem unitTangent_norm (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) (x : ℝ) :
    (F.metric t).tangentNorm (c x t) (spatialUnitTangent F c t x) = 1 := by
  rw [RiemannianMetric.tangentNorm, unitTangent_inner_self F c hc ht x, Real.sqrt_one]

end PoincareMT.M62
