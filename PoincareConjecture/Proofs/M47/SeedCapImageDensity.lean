import PoincareConjecture.Proofs.M47.SeedCapModelDensity
import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeImage










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_seed_cap_image_density (g0 : StandardInitialMetric)
    {A0 Rmax : ℝ} (hA0 : 0 < A0) (hRmax : 0 < Rmax) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M],
      ∀ (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph StandardCapSpace M),
        ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source →
        ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target →
        ∀ A : ℝ, A0 + Rmax ≤ A → e.source = g0.metric.ball 0 A →
          (∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
            g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
              2 * g0.metric.tangentNorm x v) →
          (∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
            g0.metric.tangentNorm x v ≤
              2 * g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)) →
          ∀ x ∈ g0.metric.ball 0 A0, ∀ r : ℝ, 0 < r → r ≤ Rmax →
            ENNReal.ofReal (k * r ^ 3) ≤ calibratedMetricVolume g (g.ball (e x) r) := by
  obtain ⟨k0, hk0, hmodel⟩ := exists_seed_cap_model_density g0 hA0 hRmax
  refine ⟨k0 / 64, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ g e hf hi A hA hsource hupper hlower x hx r hr hrmax
  have hball : g0.metric.ball x (r / 2) ⊆ e.source := by
    rw [hsource]
    intro y hy
    calc
      g0.metric.edist 0 y ≤ g0.metric.edist 0 x + g0.metric.edist x y :=
        M36.metric_edist_triangle g0.metric 0 x y
      _ < ENNReal.ofReal A0 + ENNReal.ofReal (r / 2) := ENNReal.add_lt_add hx hy
      _ = ENNReal.ofReal (A0 + r / 2) := (ENNReal.ofReal_add hA0.le (by positivity)).symm
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal (by linarith only [hA, hrmax, hr])
  have hvol := M34.calibrated_ball_volume_le_mul_of_tangent_bounds g0.metric g e hf hi
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    hupper hlower hball (by linarith : 2 * (r / 2) ≤ r)
  have hseed := hmodel x hx (r / 2) (half_pos hr) (by linarith only [hr, hrmax])
  have h8 : ENNReal.ofReal (2 : ℝ) ^ 3 = 8 := by norm_num
  rw [h8] at hvol
  apply (ENNReal.mul_le_mul_iff_right (a := (8 : ℝ≥0∞))
    (by norm_num) (by norm_num)).mp
  have h8real : ENNReal.ofReal (8 : ℝ) = 8 := by norm_num
  rw [← h8real, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), h8real]
  have hcalc : 8 * (k0 / 64 * r ^ 3) = k0 * (r / 2) ^ 3 := by ring
  rw [hcalc]
  exact hseed.trans hvol

end PoincareConjecture.Proofs.M47
