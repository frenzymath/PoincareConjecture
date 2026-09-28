import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.RadialComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.ScalarComparison
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]

theorem polarDensity_cross_le_on_regular_ray
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ U)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1)
    {b κ : ℝ} (hb : 0 < b) (hκ : 0 ≤ κ) (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U)
    (hi : ∀ s ∈ Icc 0 b,
      Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ)))
    (hRic : ∀ s ∈ Ioo 0 b, ∀ v : TangentSpace (𝓡 (m + 1)) (e (s • θ)),
      -(m : ℝ) * κ * g.inner (e (s • θ)) v v ≤ D.ricci (e (s • θ)) v v)
    {t s : ℝ} (ht : t ∈ Ioo 0 b) (hs : s ∈ Ioo 0 b) (hts : t ≤ s) :
    (s ^ m * g.pullbackVolumeDensity e (s • θ)) * modelS κ t ^ m ≤
      (t ^ m * g.pullbackVolumeDensity e (t • θ)) * modelS κ s ^ m := by
  let y : ℝ → ℝ := fun r => r * g.pullbackVolumeDensity e (r • θ) ^ (1 / (m : ℝ))
  have hy (r : ℝ) (hr : r ∈ Icc 0 b) : ContDiffAt ℝ ∞ y r :=
    g.contDiffAt_signed_polarDensityRoot θ m
      (he.contMDiffAt (hU.mem_nhds (hsub r hr))) (hi r hr)
  have hyd (r : ℝ) (hr : r ∈ Icc 0 b) : ContDiffAt ℝ ∞ (deriv y) r :=
    (hy r hr).derivWithin (by simp)
  have ha := antitoneOn_div_modelS_of_second_derivative_le hκ hb
    (y := y) (y' := deriv y) (y'' := deriv (deriv y))
    (fun r hr => ((hy r hr).differentiableAt (by simp)).hasDerivAt)
    (fun r hr => (hyd r hr).continuousAt.continuousWithinAt)
    (fun r hr => ((hyd r ⟨hr.1.le, hr.2.le⟩).differentiableAt (by simp)).hasDerivAt)
    (by simp [y])
    (fun r hr => g.deriv2_polarDensityRoot_le_of_ricci D hm hU h0 he hgeo hmetric
      θ hθ hb hsub hr (hi r ⟨hr.1.le, hr.2.le⟩) (hRic r hr))
  have hcross := (div_le_div_iff₀ (modelS_pos hκ hs.1) (modelS_pos hκ ht.1)).mp
    (ha ht hs hts)
  have hynonneg : 0 ≤ y s := mul_nonneg hs.1.le (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hpow := pow_le_pow_left₀ (mul_nonneg hynonneg (modelS_nonneg hκ ht.1.le)) hcross m
  simpa only [mul_pow, y, g.signed_polarDensityRoot_pow e θ hm] using hpow

end PoincareConjecture.RiemannianMetric
