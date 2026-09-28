import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.Length
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.GeodesicLength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic





















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

end PoincareConjecture.RiemannianMetric

namespace Poincare.VolumeComparison.Conjugate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem sum_energy_ge_of_endpoint_distance_lower_bound
    (g : PoincareConjecture.RiemannianMetric n M) {N : ℕ} (τ : ℕ → ℝ)
    (γ : ℕ → ℝ → M) (p : ℕ → M) {C : ℝ} (hC : 0 < C)
    (hτ : ∀ i < N, τ i ≤ τ (i + 1))
    (hγ : ∀ i < N, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (γ i) (Icc (τ i) (τ (i + 1))))
    (hcont : ∀ i < N, ContinuousOn (fun t =>
      g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1))
        (Icc (τ i) (τ (i + 1))))
    (hleft : ∀ i < N, γ i (τ i) = p i)
    (hright : ∀ i < N, γ i (τ (i + 1)) = p (i + 1))
    (hmin : ENNReal.ofReal ((τ N - τ 0) * C) ≤ g.edist (p 0) (p N)) :
    (τ N - τ 0) * C ^ 2 ≤ ∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
      (g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1)) ^ 2 := by
  let E : ℕ → ℝ := fun i => ∫ t in (τ i)..(τ (i + 1)),
    (g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1)) ^ 2
  let l : ℕ → ℝ := fun i => (E i + (τ (i + 1) - τ i) * C ^ 2) / (2 * C)
  have hl : ∀ i < N, 0 ≤ l i := by
    intro i hi
    have hE : 0 ≤ E i := intervalIntegral.integral_nonneg (hτ i hi)
      (fun _ _ => sq_nonneg _)
    exact div_nonneg (add_nonneg hE (mul_nonneg (sub_nonneg.mpr (hτ i hi))
      (sq_nonneg C))) (by positivity)
  have hd : ∀ i < N, g.edist (p i) (p (i + 1)) ≤ ENNReal.ofReal (l i) := by
    intro i hi
    rw [← hleft i hi, ← hright i hi]
    exact g.edist_le_ofReal_energy_bound (hτ i hi) hC (hγ i hi) (hcont i hi)
  have h := hmin.trans (edist_le_ofReal_sum g p l N hl hd)
  rw [ENNReal.ofReal_le_ofReal_iff
    (Finset.sum_nonneg fun i hi => hl i (Finset.mem_range.mp hi))] at h
  have hsum : ∑ i ∈ Finset.range N, (τ (i + 1) - τ i) = τ N - τ 0 := by
    clear h hl hd hmin hright hleft hcont hγ hτ
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have heq : (∑ i ∈ Finset.range N, l i) =
      ((∑ i ∈ Finset.range N, E i) + (τ N - τ 0) * C ^ 2) / (2 * C) := by
    simp only [l, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
  rw [heq] at h
  have hh := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp h
  change (τ N - τ 0) * C ^ 2 ≤ ∑ i ∈ Finset.range N, E i
  nlinarith

end Poincare.VolumeComparison.Conjugate
