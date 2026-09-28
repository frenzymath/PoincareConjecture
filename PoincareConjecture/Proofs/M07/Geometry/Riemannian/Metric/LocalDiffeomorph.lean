import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.InducedForm
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Bundle Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

noncomputable def pullbackOfLocalDiffeomorph (g : RiemannianMetric n N)
    (f : M → N) (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f) :
    RiemannianMetric n M where
  inner := inducedForm g f
  symm x v w := g.symm (f x) _ _
  pos x v hv := by
    let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      hf.mfderivToContinuousLinearEquiv (by simp) x
    apply g.pos (f x)
    intro hzero
    apply hv
    apply L.injective
    change L v = L 0
    rw [map_zero]
    exact hzero
  isVonNBounded x := by
    let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      hf.mfderivToContinuousLinearEquiv (by simp) x
    have heq : {v : EuclideanSpace ℝ (Fin n) |
        inducedForm (I := 𝓡 n) (J := 𝓡 n) g f x v v < 1} =
        L.symm.toContinuousLinearMap '' {v : EuclideanSpace ℝ (Fin n) |
          g.inner (f x) v v < 1} := by
      ext v
      constructor
      · intro hv
        exact ⟨L v, hv, L.symm_apply_apply v⟩
      · rintro ⟨w, hw, rfl⟩
        change g.inner (f x) (L (L.symm w)) (L (L.symm w)) < 1
        rw [L.apply_symm_apply]
        exact hw
    change Bornology.IsVonNBounded ℝ
      {v : EuclideanSpace ℝ (Fin n) |
        inducedForm (I := 𝓡 n) (J := 𝓡 n) g f x v v < 1}
    rw [heq]
    exact (g.isVonNBounded (f x)).image _
  contMDiff x := inducedForm_contMDiffAt g (hf.contMDiff x)

@[simp] theorem pullbackOfLocalDiffeomorph_inner (g : RiemannianMetric n N)
    (f : M → N) (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (g.pullbackOfLocalDiffeomorph f hf).inner x v w = g.inner (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) := rfl

end PoincareConjecture.RiemannianMetric
