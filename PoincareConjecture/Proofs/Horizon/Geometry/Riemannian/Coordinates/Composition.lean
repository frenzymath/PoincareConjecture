import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_comp_of_eventuallyEq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    {p q : EuclideanSpace ℝ (Fin n) → M}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hq : MDifferentiableAt (𝓡 n) (𝓡 n) q (f x))
    (hf : DifferentiableAt ℝ f x) (heq : q ∘ f =ᶠ[𝓝 x] p)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients q (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) =
      g.pullbackCoefficients p x v w := by
  have hd := mfderiv_comp x hq hf.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hd
  have hchain : (mfderiv (𝓡 n) (𝓡 n) q (f x)).comp (fderiv ℝ f x) =
      mfderiv (𝓡 n) (𝓡 n) p x := hd.symm.trans heq.mfderiv_eq
  have hv := congrArg (fun A ↦ A v) hchain
  have hw := congrArg (fun A ↦ A w) hchain
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  change g.inner (q (f x))
      (mfderiv (𝓡 n) (𝓡 n) q (f x) (fderiv ℝ f x v))
      (mfderiv (𝓡 n) (𝓡 n) q (f x) (fderiv ℝ f x w)) =
    g.inner (p x) (mfderiv (𝓡 n) (𝓡 n) p x v) (mfderiv (𝓡 n) (𝓡 n) p x w)
  erw [hv, hw, show q (f x) = p x from heq.self_of_nhds]
  rfl

end PoincareConjecture.RiemannianMetric
