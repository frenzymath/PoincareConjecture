import PoincareConjecture.Definitions.M62Curve
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem speed_nonneg (t x : ℝ) : 0 ≤ curveSpeed F c t x :=
  Real.sqrt_nonneg _

theorem speed_sq (t x : ℝ) :
    curveSpeed F c t x ^ 2 =
      (F.metric t).inner (c x t) (curveVelocity (fun y ↦ c y t) x)
        (curveVelocity (fun y ↦ c y t) x) := by
  apply Real.sq_sqrt
  exact ((F.metric t).toRiemannianMetric.toCore (c x t)).re_inner_nonneg _

theorem speed_pos (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Set.Icc a b)
    (x : ℝ) : 0 < curveSpeed F c t x := by
  exact Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hc.immersed t ht x))

theorem unitTangent_inner_self (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) (x : ℝ) :
    (F.metric t).inner (c x t) (spatialUnitTangent F c t x)
      (spatialUnitTangent F c t x) = 1 := by
  have hv := (speed_pos F c hc ht x).ne'
  simp only [spatialUnitTangent, map_smul, smul_apply, smul_eq_mul]
  rw [← speed_sq F c t x]
  field_simp

theorem unitTangent_norm (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) (x : ℝ) :
    (F.metric t).tangentNorm (c x t) (spatialUnitTangent F c t x) = 1 := by
  rw [RiemannianMetric.tangentNorm, unitTangent_inner_self F c hc ht x, Real.sqrt_one]

end PoincareConjecture.M62
