import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussEquation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M65Gauss

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
  {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}




theorem gauss_curvatureTensor_transport
    (D : LeviCivitaData g) (DE : LeviCivitaData gE) (D' : LeviCivitaData h)
    {ψ : EuclideanSpace ℝ (Fin n) → M}
    {G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hG : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ G y)
    (hψ : ∀ᶠ y in 𝓝 (G x), ContMDiffAt (𝓡 n) (𝓡 n) ∞ ψ y)
    (hinv : ∀ᶠ y in 𝓝 (G x), (mfderiv (𝓡 n) (𝓡 n) ψ y).IsInvertible)
    (hψmetric : ∀ᶠ y in 𝓝 (G x), ∀ u v : EuclideanSpace ℝ (Fin n),
      gE.inner y u v = g.inner (ψ y)
        (mfderiv (𝓡 n) (𝓡 n) ψ y u) (mfderiv (𝓡 n) (𝓡 n) ψ y v))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin m),
      h.inner y u v = g.inner ((ψ ∘ G) y)
        (mfderiv (𝓡 m) (𝓡 n) (ψ ∘ G) y u) (mfderiv (𝓡 m) (𝓡 n) (ψ ∘ G) y v))
    (u v w z : EuclideanSpace ℝ (Fin m)) :
    D'.curvatureTensor x u v w z =
      D.curvatureTensor ((ψ ∘ G) x)
        (mfderiv (𝓡 m) (𝓡 n) (ψ ∘ G) x u) (mfderiv (𝓡 m) (𝓡 n) (ψ ∘ G) x v)
        (mfderiv (𝓡 m) (𝓡 n) (ψ ∘ G) x w) (mfderiv (𝓡 m) (𝓡 n) (ψ ∘ G) x z) +
      g.inner ((ψ ∘ G) x)
        (mfderiv (𝓡 n) (𝓡 n) ψ (G x) (secondFundamentalForm DE D' G x u w))
        (mfderiv (𝓡 n) (𝓡 n) ψ (G x) (secondFundamentalForm DE D' G x v z)) -
      g.inner ((ψ ∘ G) x)
        (mfderiv (𝓡 n) (𝓡 n) ψ (G x) (secondFundamentalForm DE D' G x u z))
        (mfderiv (𝓡 n) (𝓡 n) ψ (G x) (secondFundamentalForm DE D' G x v w)) := by
  have hchain (y : EuclideanSpace ℝ (Fin m)) (hGy : ContDiffAt ℝ ∞ G y)
      (hψy : ContMDiffAt (𝓡 n) (𝓡 n) ∞ ψ (G y)) :
      mfderiv (𝓡 m) (𝓡 n) (ψ ∘ G) y =
        (mfderiv (𝓡 n) (𝓡 n) ψ (G y)).comp (fderiv ℝ G y) := by
    rw [mfderiv_comp y (hψy.mdifferentiableAt (by simp))
      (hGy.contMDiffAt.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  have hcont : ContinuousAt G x := hG.self_of_nhds.continuousAt
  have hcoord : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin m),
      h.inner y u v = gE.inner (G y) (fderiv ℝ G y u) (fderiv ℝ G y v) := by
    filter_upwards [hG, hmetric, hcont.eventually hψ, hcont.eventually hψmetric]
      with y hGy hy hψy hmetricy u v
    rw [hmetricy, hy, hchain y hGy hψy]
    rfl
  have h := gauss_curvatureTensor DE D' hG hcoord u v w z
  rw [DE.curvatureTensor_eq_pullback_euclidean D hψ.self_of_nhds hinv hψmetric] at h
  simp only [hψmetric.self_of_nhds] at h
  simpa +instances only [hchain x hG.self_of_nhds hψ.self_of_nhds,
    ContinuousLinearMap.comp_apply, Function.comp_apply] using! h

end PoincareConjecture.M65Gauss
