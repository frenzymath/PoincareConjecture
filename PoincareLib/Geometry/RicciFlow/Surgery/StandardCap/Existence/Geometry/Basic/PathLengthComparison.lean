import PoincareLib.Geometry.Riemannian.MetricComparison

/-!
# Comparing actual path lengths on different selected metrics

An interior-time bound on the actual tangent speeds bounds the full path
lengths. Endpoints have zero measure, so no unrestricted derivative at an
endpoint is assumed. Source: Morgan-Tian Theorem 12.29 and Claim 12.30,
pp. 324-325; reverse-ball-localization.md.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.RiemannianMetric

/-- A bound on actual tangent speeds in the open time interval controls
the complete path lengths, in arbitrary source and target dimensions
(Theorem 12.29, pp. 324-325). -/
theorem pathELength_le_mul_of_speed_le
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (η : ℝ → M) (γ : ℝ → N) (a b : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Ioo a b,
      g.tangentNorm (η t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) η t 1) ≤
        C * h.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 m) γ t 1)) :
    g.pathELength η a b ≤ ENNReal.ofReal C * h.pathELength γ a b := by
  rw [g.pathELength_eq_lintegral_tangentNorm, h.pathELength_eq_lintegral_tangentNorm,
    ← restrict_Ioo_eq_restrict_Icc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  exact (ENNReal.ofReal_le_ofReal (hbound t ht)).trans_eq (ENNReal.ofReal_mul hC)

end PoincareMT.RiemannianMetric
