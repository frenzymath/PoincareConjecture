import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.InverseRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasFDerivAt_inverse_radius
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {q : M} (hq : q ∈ e.target) (hpos : 0 < ‖e.symm q‖)
    (hgauss : ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner q (mfderiv (𝓡 n) (𝓡 n) e (e.symm q) (e.symm q))
        (mfderiv (𝓡 n) (𝓡 n) e (e.symm q) w) = inner ℝ (e.symm q) w) :
    HasFDerivAt
      (fun y => ‖e.symm ((extChartAt (𝓡 n) q).symm y)‖)
      (‖e.symm q‖⁻¹ •
        (show EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from
          g.inner q (mfderiv (𝓡 n) (𝓡 n) e (e.symm q) (e.symm q))))
      (extChartAt (𝓡 n) q q) := by
  have hd := g.hasFDerivAt_half_squared_inverse_radius e he hei hq hgauss
  have hsq := hd.const_mul 2
  have hcenter : (extChartAt (𝓡 n) q).symm (extChartAt (𝓡 n) q q) = q :=
    (extChartAt (𝓡 n) q).left_inv (mem_extChartAt_source q)
  have hnonzero : 2 * (‖e.symm ((extChartAt (𝓡 n) q).symm
      (extChartAt (𝓡 n) q q))‖ ^ 2 / 2) ≠ 0 := by
    rw [hcenter]
    nlinarith
  have hroot := hsq.sqrt hnonzero
  have hroot' := hroot.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => show
      ‖e.symm ((extChartAt (𝓡 n) q).symm y)‖ =
        Real.sqrt (2 * (‖e.symm ((extChartAt (𝓡 n) q).symm y)‖ ^ 2 / 2)) by
      rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.sqrt_sq (norm_nonneg _)]))
  apply hroot'.congr_fderiv
  rw [hcenter, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    Real.sqrt_sq (norm_nonneg _)]
  ext w
  simp only [smul_apply, smul_eq_mul]
  field_simp

theorem hasFDerivAt_average_inverse_radius_zero
    (g : RiemannianMetric n M)
    (e₁ e₂ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    (hei₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁.symm e₁.target)
    (hei₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂.symm e₂.target)
    {q : M} (hq₁ : q ∈ e₁.target) (hq₂ : q ∈ e₂.target)
    (hpos : 0 < ‖e₁.symm q‖) (heq : ‖e₁.symm q‖ = ‖e₂.symm q‖)
    (hgauss₁ : ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner q (mfderiv (𝓡 n) (𝓡 n) e₁ (e₁.symm q) (e₁.symm q))
        (mfderiv (𝓡 n) (𝓡 n) e₁ (e₁.symm q) w) = inner ℝ (e₁.symm q) w)
    (hgauss₂ : ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner q (mfderiv (𝓡 n) (𝓡 n) e₂ (e₂.symm q) (e₂.symm q))
        (mfderiv (𝓡 n) (𝓡 n) e₂ (e₂.symm q) w) = inner ℝ (e₂.symm q) w)
    (hopposite : mfderiv (𝓡 n) (𝓡 n) e₁ (e₁.symm q) (e₁.symm q) =
      -mfderiv (𝓡 n) (𝓡 n) e₂ (e₂.symm q) (e₂.symm q)) :
    HasFDerivAt
      (fun y => (‖e₁.symm ((extChartAt (𝓡 n) q).symm y)‖ +
        ‖e₂.symm ((extChartAt (𝓡 n) q).symm y)‖) / 2)
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (extChartAt (𝓡 n) q q) := by
  have h₁ := g.hasFDerivAt_inverse_radius e₁ he₁ hei₁ hq₁ hpos hgauss₁
  have h₂ := g.hasFDerivAt_inverse_radius e₂ he₂ hei₂ hq₂ (heq ▸ hpos) hgauss₂
  have h := ((h₁.add h₂).const_mul (1 / 2 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => show
      (‖e₁.symm ((extChartAt (𝓡 n) q).symm y)‖ +
        ‖e₂.symm ((extChartAt (𝓡 n) q).symm y)‖) / 2 =
      (1 / 2 : ℝ) * (‖e₁.symm ((extChartAt (𝓡 n) q).symm y)‖ +
        ‖e₂.symm ((extChartAt (𝓡 n) q).symm y)‖) by ring))
  apply h.congr_fderiv
  ext w
  simp [heq, hopposite]

end PoincareConjecture.RiemannianMetric
