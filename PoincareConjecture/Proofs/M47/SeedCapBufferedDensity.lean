import PoincareConjecture.Proofs.M47.SeedCapImageDensity
import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_cap_buffered_density (g0 : StandardInitialMetric)
    {Rtip Rmax : ℝ} (htip : 0 < Rtip) (hmax : 0 < Rmax) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M],
      ∀ (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph StandardCapSpace M),
        ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source →
        ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target →
        ∀ A : ℝ, 2 * Rtip + Rmax ≤ A → e.source = g0.metric.ball 0 A →
          (∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
            g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
              2 * g0.metric.tangentNorm x v) →
          (∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
            g0.metric.tangentNorm x v ≤
              2 * g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)) →
          g.ball (e 0) Rtip ⊆ e.target →
          ∀ z ∈ g.ball (e 0) Rtip, ∀ r : ℝ, 0 < r → r ≤ Rmax →
            ENNReal.ofReal (k * r ^ 3) ≤ calibratedMetricVolume g (g.ball z r) := by
  obtain ⟨k, hk, hdensity⟩ := exists_seed_cap_image_density g0
    (by positivity : 0 < 2 * Rtip) hmax
  refine ⟨k, hk, ?_⟩
  intro M _ _ _ _ _ _ _ g e hf hi A hA hsource hupper hlower hcover z hz r hr hrmax
  have hzero : (0 : StandardCapSpace) ∈ e.source := by
    rw [hsource]
    change g0.metric.edist 0 0 < ENNReal.ofReal A
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (by linarith only [hA, htip, hmax])
  have hcapture := g0.metric.ball_subset_image_ball_of_forward_tangentNorm_le
    g e hf hi hzero (by norm_num : (0 : ℝ) < 2) hcover
    (fun x hx _ => hlower x hx)
  obtain ⟨x, hx, rfl⟩ := hcapture hz
  exact hdensity M g e hf hi A hA hsource hupper hlower x hx.1 r hr hrmax

end PoincareConjecture.Proofs.M47
