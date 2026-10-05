import PoincareLib.Geometry.Riemannian.Tensor.Norm
import PoincareLib.Geometry.Riemannian.Tensor.Operations

/-!
# The intrinsic tensor norm in an arbitrary coordinate basis

The actual metric's orthonormal basis is used for the intrinsic norm;
the component basis only needs to be an algebraic basis. This supplies
the exact norm identification for the finite-jet curvature estimate in
Morgan-Tian Theorem 12.5, pp. 296-297.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Bundle

namespace PoincareMT.RiemannianMetric

/-- The inverse-Gram component expression equals the frozen intrinsic
norm whenever the raw tensor has an actual multilinear realization
(Theorem 12.5, pp. 296-297, local curvature estimate). -/
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

end PoincareMT.RiemannianMetric
