import PoincareConjecture.Proofs.M47.CanonicalNeckIsometricImage








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.Proofs.M47



theorem partialIsometry_metric_symm
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (hmetric : ∀ x ∈ D.source, ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v w = h.inner (D x) (mfderiv (𝓡 3) (𝓡 3) D x v)
        (mfderiv (𝓡 3) (𝓡 3) D x w)) :
    ∀ y ∈ D.symm.source, ∀ v w : TangentSpace (𝓡 3) y,
      h.inner y v w = g.inner (D.symm y) (mfderiv (𝓡 3) (𝓡 3) D.symm y v)
        (mfderiv (𝓡 3) (𝓡 3) D.symm y w) := by
  intro y hy v w
  have he : D.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨D.mdifferentiableOn (by simp), D.symm.mdifferentiableOn (by simp)⟩
  have hd : (mfderiv (𝓡 3) (𝓡 3) D (D.symm y)).comp
      (mfderiv (𝓡 3) (𝓡 3) D.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) y) := he.comp_symm_deriv hy
  have hv : mfderiv (𝓡 3) (𝓡 3) D (D.symm y)
      (mfderiv (𝓡 3) (𝓡 3) D.symm y v) = v := congrArg (fun A => A v) hd
  have hw : mfderiv (𝓡 3) (𝓡 3) D (D.symm y)
      (mfderiv (𝓡 3) (𝓡 3) D.symm y w) = w := congrArg (fun A => A w) hd
  have hm := hmetric (D.symm y) (D.map_target hy)
    (mfderiv (𝓡 3) (𝓡 3) D.symm y v) (mfderiv (𝓡 3) (𝓡 3) D.symm y w)
  rw [hv, hw] at hm
  have hright : D.toPartialEquiv (D.symm.toPartialEquiv y) = y := D.right_inv hy
  exact (hm.trans (congrArg (fun z : X => h.inner z v w) hright)).symm

end PoincareConjecture.Proofs.M47
