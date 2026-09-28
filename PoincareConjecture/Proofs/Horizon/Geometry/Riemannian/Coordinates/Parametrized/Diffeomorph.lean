import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.ParametrizedCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u v w

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem parametrizedCoefficients_diffeomorph
    (gM : RiemannianMetric n M) (gN : RiemannianMetric n N)
    (d : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (d x)
        (mfderiv (𝓡 n) (𝓡 n) d x v) (mfderiv (𝓡 n) (𝓡 n) d x w))
    (f : E → M) :
    gM.parametrizedCoefficients f = gN.parametrizedCoefficients (d ∘ f) := by
  funext x
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) f x
  · ext v w
    simp only [parametrizedCoefficients_apply]
    rw [hinner, mfderiv_comp x (d.mdifferentiable (by simp) (f x)) hf]
    rfl
  · have hdf : ¬ MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) (d ∘ f) x := by
      intro h
      apply hf
      have hback := (d.symm.mdifferentiable (by simp) (d (f x))).comp x h
      simpa only [Function.comp_def, d.symm_apply_apply] using hback
    ext v w
    rw [parametrizedCoefficients_apply, parametrizedCoefficients_apply,
      mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hdf]
    change gM.inner (f x) 0 0 = gN.inner (d (f x)) 0 0
    simp



theorem parametrizedCoefficients_pullbackOfDiffeomorph
    (g : RiemannianMetric n N) (d : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) (f : E → M) :
    (g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph).parametrizedCoefficients f =
      g.parametrizedCoefficients (d ∘ f) :=
  parametrizedCoefficients_diffeomorph _ g d (fun _ _ _ => rfl) f

end PoincareConjecture.RiemannianMetric

namespace Diffeomorph

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem isInvertible_mfderiv_comp (d : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    {f : E → M} {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) f x)
    (hi : (mfderiv 𝓘(ℝ, E) (𝓡 n) f x).IsInvertible) :
    (mfderiv 𝓘(ℝ, E) (𝓡 n) (d ∘ f) x).IsInvertible := by
  rw [mfderiv_comp x (d.mdifferentiable (by simp) (f x)) hf]
  exact (show (mfderiv (𝓡 n) (𝓡 n) d (f x)).IsInvertible from
    ⟨d.mfderivToContinuousLinearEquiv (by simp) (f x), rfl⟩).comp hi

end Diffeomorph
