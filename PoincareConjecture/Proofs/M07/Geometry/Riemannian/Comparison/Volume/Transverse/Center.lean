import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Density
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullbackVolumeDensity_zero_eq_one
    (g : RiemannianMetric n M) (e : EuclideanSpace ℝ (Fin n) → M)
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin n),
      g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 u)
      (mfderiv (𝓡 n) (𝓡 n) e 0 v) = inner ℝ u v) :
    g.pullbackVolumeDensity e 0 = 1 := by
  have hgram : Matrix.of (fun i j : Fin n => g.inner (e 0)
      (mfderiv (𝓡 n) (𝓡 n) e 0 (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) e 0 (EuclideanSpace.basisFun (Fin n) ℝ j))) = 1 := by
    ext i j
    rw [Matrix.of_apply, hmetric]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i j
  simp only [pullbackVolumeDensity, hgram, Matrix.det_one, Real.sqrt_one]

theorem contDiffAt_signed_polarDensityRoot
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    (θ : EuclideanSpace ℝ (Fin n)) (m : ℕ) {t : ℝ}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (t • θ))
    (hi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e (t • θ))) :
    ContDiffAt ℝ ∞ (fun s : ℝ =>
      s * g.pullbackVolumeDensity e (s • θ) ^ (1 / (m : ℝ))) t := by
  obtain ⟨hρ, hp⟩ := g.contDiffAt_pullbackVolumeDensity he hi
  have hline : ContDiffAt ℝ ∞ (fun s : ℝ => s • θ) t := by fun_prop
  exact contDiffAt_id.mul
    ((hρ.comp (f := fun s : ℝ => s • θ) t hline).rpow_const_of_ne hp.ne')

theorem hasDerivAt_signed_polarDensityRoot_zero
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e 0)
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin n),
      g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 u)
      (mfderiv (𝓡 n) (𝓡 n) e 0 v) = inner ℝ u v)
    (θ : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    HasDerivAt (fun s : ℝ =>
      s * g.pullbackVolumeDensity e (s • θ) ^ (1 / (m : ℝ))) 1 0 := by
  have hi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e 0) := by
    intro u v huv
    have h := hmetric (u - v) (u - v)
    simp only [map_sub, huv, sub_self, map_zero] at h
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin n))).mp h.symm)
  obtain ⟨hρ, hp⟩ := g.contDiffAt_pullbackVolumeDensity he hi
  have hline : ContDiffAt ℝ ∞ (fun s : ℝ => s • θ) 0 := by fun_prop
  have hρ0 : ContDiffAt ℝ ∞ (fun s : ℝ => g.pullbackVolumeDensity e (s • θ)) 0 := by
    have hρ' : ContDiffAt ℝ ∞ (g.pullbackVolumeDensity e) ((0 : ℝ) • θ) := by
      simpa only [zero_smul] using hρ
    exact hρ'.comp (f := fun s : ℝ => s • θ) 0 hline
  have hr := hρ0.rpow_const_of_ne (p := 1 / (m : ℝ)) (by simpa using hp.ne')
  simpa [g.pullbackVolumeDensity_zero_eq_one e hmetric] using!
    (hasDerivAt_id (0 : ℝ)).mul (hr.differentiableAt (by simp)).hasDerivAt

theorem signed_polarDensityRoot_pow
    (g : RiemannianMetric n M) (e : EuclideanSpace ℝ (Fin n) → M)
    (θ : EuclideanSpace ℝ (Fin n)) {m : ℕ} (hm : 0 < m) (t : ℝ) :
    (t * g.pullbackVolumeDensity e (t • θ) ^ (1 / (m : ℝ))) ^ m =
      t ^ m * g.pullbackVolumeDensity e (t • θ) := by
  have hρ : 0 ≤ g.pullbackVolumeDensity e (t • θ) := Real.sqrt_nonneg _
  have hpow : (g.pullbackVolumeDensity e (t • θ) ^ (1 / (m : ℝ))) ^ m =
      g.pullbackVolumeDensity e (t • θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ,
      one_div_mul_cancel (Nat.cast_ne_zero.mpr hm.ne'), Real.rpow_one]
  rw [mul_pow, hpow]

end PoincareConjecture.RiemannianMetric
