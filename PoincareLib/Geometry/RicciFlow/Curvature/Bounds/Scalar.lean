import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.ScalarTrace
import PoincareLib.Analysis.Parabolic.Maximum.ScalarComparison
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/Ch04/ScalarBounds.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. See the curvature import record under
`references/ricci-flow/mapher/curvature/`. -/

/-!
# Negative scalar-curvature bounds

These application proofs combine explicit geometric and analytic inputs.
They implement the corrected negative comparison in Morgan-Tian, printed
pp. 64-65, and the absolute-time three-dimensional bound on printed pp. 79-80.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.RicciFlow

section GeneralDimension

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- At a spatial scalar minimum, the actual evolution velocity dominates the scalar reaction. -/
theorem scalarCurvature_velocity_lowerBound {J : Set ℝ} (F : RicciFlow n M J)
    (hn : 0 < n) (t : ℝ) (ht : t ∈ J) (x : M)
    (hmin : ∀ y : M,
      (F.connection t).scalarCurvature x ≤ (F.connection t).scalarCurvature y) :
    (2 / (n : ℝ)) * ((F.connection t).scalarCurvature x) ^ 2 ≤
      (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x := by
  have hL := (F.connection t).laplacian_nonneg_of_isLocalMinAt
    ((F.contMDiff_scalarCurvature t ht).contMDiffAt (x := x))
    (Filter.Eventually.of_forall hmin)
  have hR := (F.connection t).scalarCurvature_sq_le x
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiv : ((F.connection t).scalarCurvature x) ^ 2 / (n : ℝ) ≤
      (F.connection t).ricciNormSq x := (div_le_iff₀ hnR).mpr (by nlinarith)
  calc
    (2 / (n : ℝ)) * ((F.connection t).scalarCurvature x) ^ 2 =
        2 * (((F.connection t).scalarCurvature x) ^ 2 / (n : ℝ)) := by ring
    _ ≤ _ := by linarith

/-- A strictly negative global initial lower bound propagates by the corrected scalar comparison.
-/
theorem scalarCurvature_lowerBound [CompactSpace M] {a b : ℝ}
    (F : RicciFlow n M (Set.Ico a b)) (hab : a < b) (hn : 0 < n)
    (r0 : ℝ) (hr0 : r0 < 0)
    (hinit : ∀ x : M, r0 ≤ (F.connection a).scalarCurvature x) :
    ∀ t ∈ Set.Ico a b, ∀ x : M,
      r0 / (1 - 2 * r0 * (t - a) / (n : ℝ)) ≤
        (F.connection t).scalarCurvature x := by
  exact compact_min_velocity_lower_bound hab hn hr0
    (fun t x ↦ (F.connection t).scalarCurvature x)
    (fun t x ↦ (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x)
    F.contMDiffOn_scalarCurvature.continuousOn
    F.hasDerivWithinAt_scalarCurvature
    (F.scalarCurvature_velocity_lowerBound hn) hinit

end GeneralDimension

/-- The three-dimensional normalized lower bound preserves the absolute time clock. -/
theorem scalarCurvature_lowerBound_three
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] {a b : ℝ}
    (F : RicciFlow 3 M (Set.Ico a b)) (ha : 0 ≤ a) (hab : a < b)
    (hinit : ∀ x : M, -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x) :
    ∀ t ∈ Set.Ico a b, ∀ x : M,
      -6 / (1 + 4 * t) ≤ (F.connection t).scalarCurvature x := by
  have hda : 0 < 1 + 4 * a := by positivity
  have hr0 : -6 / (1 + 4 * a) < 0 := div_neg_of_neg_of_pos (by norm_num) hda
  have h := F.scalarCurvature_lowerBound hab (by norm_num) _ hr0 hinit
  intro t ht x
  have hdt : 0 < 1 + 4 * t := by linarith [ht.1]
  have hformula : (-6 / (1 + 4 * a)) /
      (1 - 2 * (-6 / (1 + 4 * a)) * (t - a) / (3 : ℝ)) = -6 / (1 + 4 * t) := by
    have hden : 1 - 2 * (-6 / (1 + 4 * a)) * (t - a) / (3 : ℝ) =
        (1 + 4 * t) / (1 + 4 * a) := by
      field_simp
      ring
    rw [hden]
    field_simp [ne_of_gt hda, ne_of_gt hdt]
  simpa only [Nat.cast_ofNat, hformula] using h t ht x

end PoincareMT.RicciFlow
