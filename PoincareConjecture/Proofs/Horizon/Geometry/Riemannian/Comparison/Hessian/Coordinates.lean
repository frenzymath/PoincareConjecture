import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hessian_in_smooth_local_parametrization (D : LeviCivitaData g)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hB : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ B.source)
    {f : M → ℝ} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (B x))
    (v w : EuclideanSpace ℝ (Fin n)) :
    D.hessian f (B x) (mfderiv (𝓡 n) (𝓡 n) B x v)
        (mfderiv (𝓡 n) (𝓡 n) B x w) =
      fderiv ℝ (fderiv ℝ (f ∘ B)) x v w -
        fderiv ℝ (f ∘ B) x
          (CoordinateExponential.christoffelBilinear (g.pullbackCoefficients B) x v w) := by
  have hD : B.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨hB.mdifferentiableOn (by simp), hBi.mdifferentiableOn (by simp)⟩
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ B.source) :
      (mfderiv (𝓡 n) (𝓡 n) B y).IsInvertible := ⟨hD.mfderiv hy, rfl⟩
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients B) B.source := by
    intro y hy
    exact (g.contDiffAt_pullbackCoefficients
      (hB.contMDiffAt (B.open_source.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hVo, hxV, _, hE⟩ :=
    RiemannianMetric.exists_local_realization B.open_source hx
      (g.pullbackCoefficients B) hcoeff (fun y _ a b => g.symm _ _ _)
      (fun y hy a ha => by
        apply g.pos (B y)
        intro hzero
        apply ha
        apply (hi y hy).injective
        rw [map_zero]
        exact hzero)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients B := by
    filter_upwards [hVo.mem_nhds hxV] with y hy
    exact hE y hy
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) B y).IsInvertible :=
    Filter.mem_of_superset (B.open_source.mem_nhds hx) hi
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : EuclideanSpace ℝ (Fin n),
      gE.inner y a b = g.inner (B y)
        (mfderiv (𝓡 n) (𝓡 n) B y a) (mfderiv (𝓡 n) (𝓡 n) B y b) := by
    filter_upwards [heq] with y hy a b
    exact congrArg (fun C => C a b) hy
  have hΓ : CoordinateExponential.christoffelBilinear gE.euclideanCoefficients x =
      CoordinateExponential.christoffelBilinear (g.pullbackCoefficients B) x := by
    simp only [CoordinateExponential.christoffelBilinear, heq.self_of_nhds, heq.fderiv_eq]
  rw [← DE.hessian_comp_of_metric_pullback D
    (hB.contMDiffAt (B.open_source.mem_nhds hx)) hinv hmetric hf,
    DE.hessian_eq_fderiv_sub_christoffel
      (contMDiffAt_iff_contDiffAt.mp
        (hf.comp x (hB.contMDiffAt (B.open_source.mem_nhds hx)))), hΓ]

end PoincareConjecture.LeviCivitaData
