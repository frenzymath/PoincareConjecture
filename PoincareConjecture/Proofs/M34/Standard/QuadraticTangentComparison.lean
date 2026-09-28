import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

theorem tangentNorm_le_two_sqrt_mul_of_half_inner_le
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    {x : M} {y : N} (v : TangentSpace (𝓡 n) x) (w : TangentSpace (𝓡 m) y)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hbound : (1 / 2 : ℝ) * g.inner x v v ≤ Q * h.inner y w w) :
    g.tangentNorm x v ≤ 2 * Real.sqrt Q * h.tangentNorm y w := by
  have hh : 0 ≤ h.inner y w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (h.pos y w hw).le
  change Real.sqrt (g.inner x v v) ≤ 2 * Real.sqrt Q * Real.sqrt (h.inner y w w)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hh]
  nlinarith [mul_nonneg hQ hh]

end PoincareConjecture.RiemannianMetric
