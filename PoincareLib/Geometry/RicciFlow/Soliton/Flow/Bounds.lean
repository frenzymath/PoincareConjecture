import PoincareLib.Geometry.RicciFlow.Soliton.Basic
import PoincareLib.Geometry.Riemannian.Curvature.NormBounds

/-!
# Hessian bounds for shrinking soliton potentials

The soliton equation and the bounded full curvature norm give a uniform
quadratic bound for the Hessian. This is the growth estimate used to extend
the gradient trajectories in the soliton flow construction.

Source: Morgan--Tian, Chapter 3, Section 2; Theorem 9.42, pp. 206-208.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.GradientShrinkingSolitonData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- The soliton equation bounds the whole Hessian quadratic form uniformly. -/
theorem exists_hessian_quadratic_bound (S : GradientShrinkingSolitonData n M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      |S.connection.hessian S.potential x v v| ≤ C * S.metric.inner x v v := by
  obtain ⟨K, hK, hbound⟩ := S.bounded_curvature
  refine ⟨1 / 2 + (n : ℝ) ^ 3 * K, by positivity, ?_⟩
  intro x v
  have hv : 0 ≤ S.metric.inner x v v := by
    by_cases h : v = 0
    · simp [h]
    · exact (S.metric.pos x v h).le
  have hric := S.connection.abs_ricci_quadratic_le_curvatureTensorNorm x v
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  simp only [Fintype.card_fin, hdim] at hric
  have hcurv : S.connection.curvatureTensorNorm x ≤ K :=
    (le_abs_self _).trans (hbound x)
  have hric' : |S.connection.ricci x v v| ≤ (n : ℝ) ^ 3 * K *
      S.metric.inner x v v :=
    hric.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcurv (by positivity)) hv)
  have hess : S.connection.hessian S.potential x v v =
      (1 / 2 : ℝ) * S.metric.inner x v v - S.connection.ricci x v v := by
    linarith [S.soliton_equation x v v]
  rw [hess]
  calc
    |(1 / 2 : ℝ) * S.metric.inner x v v - S.connection.ricci x v v| ≤
        |(1 / 2 : ℝ) * S.metric.inner x v v| + |S.connection.ricci x v v| :=
      abs_sub _ _
    _ ≤ (1 / 2 : ℝ) * S.metric.inner x v v +
        (n : ℝ) ^ 3 * K * S.metric.inner x v v := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hv)]
      exact add_le_add_right hric' _
    _ = (1 / 2 + (n : ℝ) ^ 3 * K) * S.metric.inner x v v := by ring

end PoincareMT.GradientShrinkingSolitonData
