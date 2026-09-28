import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Norm
import PoincareConjecture.Definitions.Ch01.TensorOperators










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Bundle

namespace PoincareConjecture.RiemannianMetric




theorem tensorNormFromComponents_eq_tensorNorm
    {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (T : CovariantTensorEvaluation n M k)
    (x : M) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x))
    (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin k => TangentSpace (𝓡 n) x) ℝ,
      ∀ v, T x v = A v) :
    tensorNormFromComponents (Matrix.of (fun i j => g.inner x (b i) (b j)))
      (fun I : Fin k → ι => T x (fun j => b (I j))) = g.tensorNorm T x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hT
  have h := tensorNormFromComponents_eq_sqrt_sum A b (g.orthonormalBasis x)
  unfold tensorNorm
  simp_rw [hA]
  exact h

end PoincareConjecture.RiemannianMetric
