import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.MinimalVariation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Piece
















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace Poincare.VolumeComparison.Conjugate

open PoincareConjecture.ConjugateVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem sum_chartEnergy_ge_of_endpoint_distance_lower_bound
    (g : PoincareConjecture.RiemannianMetric n M) {N : ℕ} (τ : ℕ → ℝ)
    (α : ℕ → M) (u : ℕ → ℝ × ℝ → EuclideanSpace ℝ (Fin n)) (p : ℕ → M)
    {s C : ℝ} (hC : 0 < C)
    (hτ : ∀ i < N, τ i ≤ τ (i + 1))
    (hu : ∀ i < N, ContDiff ℝ 3 (u i))
    (hmem : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
      u i (s, t) ∈ (extChartAt (𝓡 n) (α i)).target)
    (hleft : ∀ i < N, (extChartAt (𝓡 n) (α i)).symm (u i (s, τ i)) = p i)
    (hright : ∀ i < N,
      (extChartAt (𝓡 n) (α i)).symm (u i (s, τ (i + 1))) = p (i + 1))
    (hmin : ENNReal.ofReal ((τ N - τ 0) * C) ≤ g.edist (p 0) (p N)) :
    (1 / 2 : ℝ) * (τ N - τ 0) * C ^ 2 ≤ ∑ i ∈ Finset.range N,
      ∫ t in (τ i)..(τ (i + 1)), energyDensity
        (g.pullbackCoefficients (extChartAt (𝓡 n) (α i)).symm) (u i) (0, 1) (s, t) := by
  let γ : ℕ → ℝ → M := fun i => (extChartAt (𝓡 n) (α i)).symm ∘ (fun t => u i (s, t))
  have hus (i : ℕ) (hi : i < N) : ContDiff ℝ 3 (fun t => u i (s, t)) :=
    (hu i hi).comp (contDiff_const.prodMk contDiff_id)
  have hf (i : ℕ) (hi : i < N) (t : ℝ) (ht : t ∈ Icc (τ i) (τ (i + 1))) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) (α i)).symm (u i (s, t)) :=
    (contMDiffOn_extChartAt_symm (α i)).contMDiffAt
      ((isOpen_extChartAt_target (α i)).mem_nhds (hmem i hi t ht))
  have hγ (i : ℕ) (hi : i < N) :
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (γ i) (Icc (τ i) (τ (i + 1))) := by
    intro t ht
    exact (((hf i hi t ht).of_le (by simp)).comp t
      (((hus i hi).of_le (by norm_num)).contDiffAt.contMDiffAt)).contMDiffWithinAt
  have hc (i : ℕ) (hi : i < N) : ContinuousOn (fun t =>
      g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1))
        (Icc (τ i) (τ (i + 1))) :=
    g.continuousOn_speed_chart_comp (α i)
      (fun _ _ => ((hus i hi).of_le (by norm_num)).contDiffAt) (hmem i hi)
  have hd (i : ℕ) (hi : i < N) (t : ℝ) (ht : t ∈ Icc (τ i) (τ (i + 1))) :
      (g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1)) ^ 2 =
        2 * energyDensity (g.pullbackCoefficients (extChartAt (𝓡 n) (α i)).symm)
          (u i) (0, 1) (s, t) := by
    refine (g.tangentNorm_comp_sq_eq_pullback
      ((hf i hi t ht).mdifferentiableAt (by simp))
      ((hus i hi).differentiable (by norm_num) t)).trans ?_
    have hv : deriv (fun t => u i (s, t)) t = fderiv ℝ (u i) (s, t) (0, 1) :=
      (((hu i hi).differentiable (by norm_num) (s, t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))).deriv
    rw [hv, energyDensity]
    ring_nf
    rfl
  have h := sum_energy_ge_of_endpoint_distance_lower_bound g τ γ p hC hτ hγ hc hleft hright hmin
  have heq : (∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
      (g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1)) ^ 2) =
        2 * (∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)), energyDensity
          (g.pullbackCoefficients (extChartAt (𝓡 n) (α i)).symm) (u i) (0, 1) (s, t)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hd i (Finset.mem_range.mp hi) t
      (by simpa only [uIcc_of_le (hτ i (Finset.mem_range.mp hi))] using ht)
  rw [heq] at h
  linarith



theorem isLocalMin_sum_chartEnergy_of_endpoint_distance_lower_bound
    (g : PoincareConjecture.RiemannianMetric n M) {N : ℕ} (τ : ℕ → ℝ)
    (α : ℕ → M) (u : ℕ → ℝ × ℝ → EuclideanSpace ℝ (Fin n)) (p : ℕ → ℝ → M)
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hτ : ∀ i < N, τ i ≤ τ (i + 1))
    (hu : ∀ i < N, ContDiff ℝ 3 (u i))
    (hmem : ∀ s ∈ Ioo (-ε) ε, ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
      u i (s, t) ∈ (extChartAt (𝓡 n) (α i)).target)
    (hleft : ∀ s ∈ Ioo (-ε) ε, ∀ i < N,
      (extChartAt (𝓡 n) (α i)).symm (u i (s, τ i)) = p i s)
    (hright : ∀ s ∈ Ioo (-ε) ε, ∀ i < N,
      (extChartAt (𝓡 n) (α i)).symm (u i (s, τ (i + 1))) = p (i + 1) s)
    (hmin : ∀ s ∈ Ioo (-ε) ε,
      ENNReal.ofReal ((τ N - τ 0) * C) ≤ g.edist (p 0 s) (p N s))
    (hzero : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), energyDensity
      (g.pullbackCoefficients (extChartAt (𝓡 n) (α i)).symm) (u i) (0, 1) (0, t) =
        (1 / 2 : ℝ) * C ^ 2) :
    IsLocalMin (fun s => ∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
      energyDensity (g.pullbackCoefficients (extChartAt (𝓡 n) (α i)).symm)
        (u i) (0, 1) (s, t)) 0 := by
  have hsum : ∑ i ∈ Finset.range N, (τ (i + 1) - τ i) = τ N - τ 0 := by
    clear hzero hmin hright hleft hmem hu hτ
    induction N with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  have heq : (∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
      energyDensity (g.pullbackCoefficients (extChartAt (𝓡 n) (α i)).symm)
        (u i) (0, 1) (0, t)) = (1 / 2 : ℝ) * (τ N - τ 0) * C ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range N, (τ (i + 1) - τ i) * ((1 / 2 : ℝ) * C ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← smul_eq_mul, ← intervalIntegral.integral_const]
        apply intervalIntegral.integral_congr
        intro t ht
        exact hzero i (Finset.mem_range.mp hi) t
          (by simpa only [uIcc_of_le (hτ i (Finset.mem_range.mp hi))] using ht)
      _ = _ := by rw [← Finset.sum_mul, hsum]; ring
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hε) hε] with s hs
  change (∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
      energyDensity (g.pullbackCoefficients (extChartAt (𝓡 n) (α i)).symm)
        (u i) (0, 1) (0, t)) ≤ _
  rw [heq]
  exact sum_chartEnergy_ge_of_endpoint_distance_lower_bound g τ α u (fun i => p i s) hC hτ hu
    (hmem s hs) (hleft s hs) (hright s hs) (hmin s hs)

end Poincare.VolumeComparison.Conjugate
