import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Scalar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]

theorem laplacian_inverse_branch_le_of_polar_comparison
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1)
    {b t k : ℝ} (ht : t ∈ Ioo 0 b) (hk : 0 ≤ k)
    (hρ : DifferentiableAt ℝ (g.pullbackVolumeDensity e) (t • θ))
    (hρpos : 0 < g.pullbackVolumeDensity e (t • θ))
    (hcross : ∀ u ∈ Ioo 0 b, ∀ v ∈ Ioo 0 b, u ≤ v →
      (v ^ m * g.pullbackVolumeDensity e (v • θ)) * modelS (k ^ 2) u ^ m ≤
        (u ^ m * g.pullbackVolumeDensity e (u • θ)) * modelS (k ^ 2) v ^ m)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1))) M)
    (heB : EqOn e B B.source)
    (hB : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ B.symm B.target)
    (htB : t • θ ∈ B.source)
    (hgauss : ∀ᶠ y in 𝓝 (t • θ), ∀ v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e y) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y y)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y v) = inner ℝ y v) :
    D.laplacian (fun y => ‖B.symm y‖) (e (t • θ)) ≤ (m : ℝ) / t + (m : ℝ) * k := by
  let ρ : ℝ → ℝ := fun s => g.pullbackVolumeDensity e (s • θ)
  have hd : HasDerivAt ρ (fderiv ℝ (g.pullbackVolumeDensity e) (t • θ) θ) t := by
    simpa using! hρ.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const θ)
  have hlog := radial_logarithmic_derivative_le_of_cross hm (sq_nonneg k) ht
    hd.differentiableAt hρpos hcross
  have hnorm : ‖t • θ‖ = t := by
    rw [norm_smul, Real.norm_of_nonneg ht.1.le, hθ, mul_one]
  have hne : t • θ ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    exact ht.1.ne' hnorm.symm
  rw [g.laplacian_inverse_branch D B heB hB hBi htB hne hgauss,
    hnorm, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    map_smul, smul_eq_mul, mul_div_mul_left _ _ ht.1.ne', ← hd.deriv]
  calc
    (m : ℝ) / t + deriv ρ t / ρ t ≤
        (m : ℝ) * Real.cosh (Real.sqrt (k ^ 2) * t) / modelS (k ^ 2) t := hlog
    _ ≤ (m : ℝ) / t + (m : ℝ) * k := by
      have h := mul_le_mul_of_nonneg_left (model_logarithmic_derivative_le hk ht.1)
        (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      simpa only [← mul_div_assoc, mul_add, mul_one] using h

end PoincareConjecture.RiemannianMetric
