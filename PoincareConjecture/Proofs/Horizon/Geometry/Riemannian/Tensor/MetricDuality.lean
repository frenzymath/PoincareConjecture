import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction


set_option autoImplicit false
open scoped BigOperators

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

lemma linear_apply_eq_inverse_gram (L : E →ₗ[ℝ] ℝ) (v : E)
    (b : Module.Basis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    L v = ∑ i, ∑ j, (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ i j *
      (inner ℝ v (b i) * L (b j)) := by
  let B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u w => inner ℝ v u * L w)
    (by intros; simp [inner_add_right, add_mul])
    (by intros; simp [real_inner_smul_right, mul_assoc])
    (by intros; simp [mul_add])
    (by intros; simp [mul_left_comm])
  have hexp := congrArg L (c.sum_repr' v)
  simp only [map_sum, map_smul, smul_eq_mul] at hexp
  calc
    L v = ∑ a, inner ℝ v (c a) * L (c a) := by
      simpa only [real_inner_comm v] using hexp.symm
    _ = _ := bilinear_sum_basis_eq_inverse_gram B b c

end PoincareConjecture

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.IsSmoothCovariantTensor

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


lemma update_eq_sum (g : RiemannianMetric n M) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) (i : Fin k)
    (w : TangentSpace (𝓡 n) x) :
    T x (Function.update v i w) =
      ∑ j, g.inner x w (g.orthonormalBasis x j) *
        T x (Function.update v i (g.orthonormalBasis x j)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hT.1 x
  have h := congrArg (A.toLinearMap v i) ((g.orthonormalBasis x).sum_repr' w)
  simp only [map_sum, map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply, ← hA] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  rfl

end PoincareConjecture.IsSmoothCovariantTensor
