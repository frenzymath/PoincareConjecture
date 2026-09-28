import PoincareConjecture.Proofs.M34.Standard.QuadraticTangentComparison










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric




theorem tangentNorm_le_two_div_sqrt_mul_of_scaled_inner_le
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    {x : M} {y : N} (v : TangentSpace (𝓡 n) x) (w : TangentSpace (𝓡 m) y)
    {Q : ℝ} (hQ : 0 < Q)
    (hbound : Q * h.inner y w w ≤ 2 * g.inner x v v) :
    h.tangentNorm y w ≤ (2 / Real.sqrt Q) * g.tangentNorm x v := by
  have hg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hprod : Real.sqrt Q * h.tangentNorm y w ≤ 2 * g.tangentNorm x v := by
    change Real.sqrt Q * Real.sqrt (h.inner y w w) ≤ 2 * Real.sqrt (g.inner x v v)
    rw [← Real.sqrt_mul hQ.le]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hg]
    nlinarith
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr hQ)).mpr (by simpa only [mul_comm] using hprod)

end PoincareConjecture.RiemannianMetric
