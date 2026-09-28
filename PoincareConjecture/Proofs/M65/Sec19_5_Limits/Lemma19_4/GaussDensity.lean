import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalRicciNormal










noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Manifold Bundle Topology BigOperators

namespace PoincareConjecture




theorem m65PlaneRicciTraceDensity_gauss
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    {h : RiemannianMetric 2 LoopPlane}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : LoopPlane → EuclideanSpace ℝ (Fin 3)} {z : LoopPlane}
    (hf : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ f y)
    (hmetric : ∀ᶠ y in 𝓝 z, ∀ a b, h.inner y a b =
      g.inner (f y) (fderiv ℝ f y a) (fderiv ℝ f y b))
    {c : ℝ} (hc : 0 < c)
    (hconf : m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (N : EuclideanSpace ℝ (Fin 3)) (hN : g.inner (f z) N N = 1)
    (hNT : ∀ v, g.inner (f z) N (fderiv ℝ f z v) = 0) :
    let b := h.orthonormalBasis z
    let B := M65Gauss.secondFundamentalForm D D' f z
    m65PlaneRicciTraceDensity D f z = c / 2 *
      (D.scalarCurvature (f z) + D'.scalarCurvature z -
        g.inner (f z) (∑ i, B (b i) (b i)) (∑ i, B (b i) (b i)) +
          ∑ i, ∑ j, g.inner (f z) (B (b i) (b j)) (B (b i) (b j))) := by
  have hg := M65Gauss.gauss_scalarCurvature D D' hf hmetric N hN hNT
  have hr := m65PlaneRicciTraceDensity_eq_scalar_sub_normal D f z hc hconf N hN
    (fun i => by
      simpa +instances only [mfderiv_eq_fderiv] using!
        hNT (EuclideanSpace.basisFun (Fin 2) ℝ i))
  dsimp only at hg ⊢
  rw [hr]
  linear_combination -(c / 2) * hg

end PoincareConjecture
