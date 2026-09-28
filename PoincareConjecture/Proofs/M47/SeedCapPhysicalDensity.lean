import PoincareConjecture.Proofs.M47.SeedCapBufferedDensity
import PoincareConjecture.Proofs.M47.SeedDensityScaling








set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_seed_cap_physical_density (g0 : StandardInitialMetric)
    {Rtip Rmax : ℝ} (htip : 0 < Rtip) (hmax : 0 < Rmax) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M],
      ∀ (g : RiemannianMetric 3 M) (Q : ℝ) (hQ : 0 < Q),
      ∀ (e : OpenPartialHomeomorph StandardCapSpace M),
        ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source →
        ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target →
        ∀ A : ℝ, 2 * Rtip + Rmax ≤ A → e.source = g0.metric.ball 0 A →
          (∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
            RiemannianMetric.tangentNorm (M13.scaleSmoothMetric g Q hQ) (e x)
              (mfderiv (𝓡 3) (𝓡 3) e x v) ≤ 2 * g0.metric.tangentNorm x v) →
          (∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
            g0.metric.tangentNorm x v ≤
              2 * RiemannianMetric.tangentNorm (M13.scaleSmoothMetric g Q hQ) (e x)
                (mfderiv (𝓡 3) (𝓡 3) e x v)) →
          RiemannianMetric.ball (M13.scaleSmoothMetric g Q hQ) (e 0) Rtip ⊆ e.target →
          ∀ z ∈ RiemannianMetric.ball (M13.scaleSmoothMetric g Q hQ) (e 0) Rtip,
            ∀ r : ℝ, 0 < r → Real.sqrt Q * r ≤ Rmax →
              ENNReal.ofReal (k * r ^ 3) ≤ calibratedMetricVolume g (g.ball z r) := by
  obtain ⟨k, hk, hdensity⟩ := exists_seed_cap_buffered_density g0 htip hmax
  refine ⟨k, hk, ?_⟩
  intro M _ _ _ _ _ _ _ g Q hQ e hf hi A hA hsource hupper hlower hcover z hz r hr hmaxr
  exact seed_density_of_scaled_density g hQ z k r
    (hdensity M (M13.scaleSmoothMetric g Q hQ) e hf hi A hA hsource hupper hlower hcover
      z hz (Real.sqrt Q * r) (mul_pos (Real.sqrt_pos.mpr hQ) hr) hmaxr)

end PoincareConjecture.Proofs.M47
