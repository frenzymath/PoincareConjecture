import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Norm
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Operations










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture


theorem abs_multilinear_apply_le_orthonormal_tensor_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (A : MultilinearMap ℝ (fun _ : σ => E) ℝ)
    (b : OrthonormalBasis ι ℝ E) (v : σ → E) :
    |A v| ≤ Real.sqrt (∑ i : σ → ι, (A (fun r => b (i r))) ^ 2) *
      ∏ r, ‖v r‖ := by
  classical
  have hcoeff : (∑ i : σ → ι, (∏ r, b.toBasis.repr (v r) (i r)) ^ 2) =
      (∏ r, ‖v r‖) ^ 2 := by
    simp_rw [← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun r i => (b.toBasis.repr (v r) i) ^ 2)]
    apply Finset.prod_congr rfl
    intro r _
    simp only [OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    exact b.sum_sq_inner_right (v r)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : σ → ι => ∏ r, b.toBasis.repr (v r) (i r))
    (fun i : σ → ι => A (fun r => b (i r)))
  have hexp := multilinear_apply_basis_expansion A b.toBasis v
  simp only [OrthonormalBasis.coe_toBasis] at hexp
  rw [← hexp, hcoeff] at hcs
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow,
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  nlinarith only [hcs]

section Manifold

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem abs_tensor_evaluation_le_tensorNorm
    (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (x : M)
    (A : MultilinearMap ℝ (fun _ : Fin k => TangentSpace (𝓡 n) x) ℝ)
    (hA : ∀ v, T x v = A v) (v : Fin k → TangentSpace (𝓡 n) x) :
    |T x v| ≤ g.tensorNorm T x * ∏ r, g.tangentNorm x (v r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hnorm (q : TangentSpace (𝓡 n) x) : g.tangentNorm x q = ‖q‖ := by
    change Real.sqrt (inner ℝ q q) = ‖q‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg q)]
  have hN : g.tensorNorm T x =
      Real.sqrt (∑ i : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (A (fun r => b (i r))) ^ 2) := by
    simp_rw [← hA]
    dsimp only [RiemannianMetric.tensorNorm]
  have h := abs_multilinear_apply_le_orthonormal_tensor_norm A b v
  rw [← hN] at h
  simpa [← hA, hnorm, Fin.prod_univ_succ, mul_assoc] using h



theorem abs_tensor_orthonormal_component_le_tensorNorm
    (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (x : M)
    (A : MultilinearMap ℝ (fun _ : Fin k => TangentSpace (𝓡 n) x) ℝ)
    (hA : ∀ v, T x v = A v)
    (i : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    |T x (fun r => g.orthonormalBasis x (i r))| ≤ g.tensorNorm T x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := abs_tensor_evaluation_le_tensorNorm g T x A hA
    (fun r => g.orthonormalBasis x (i r))
  have hb (r : Fin k) : g.tangentNorm x (g.orthonormalBasis x (i r)) = 1 := by
    change Real.sqrt (inner ℝ (g.orthonormalBasis x (i r))
      (g.orthonormalBasis x (i r))) = 1
    rw [real_inner_self_eq_norm_sq,
      (g.orthonormalBasis x).norm_eq_one, one_pow]
    norm_num
  simpa [hb, ← hA, Fin.prod_univ_succ, mul_assoc] using h

end Manifold

end PoincareConjecture
