import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Pairing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.GradientTime

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture

private theorem abs_sum_mul_le_sqrt_sq {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) :
    |∑ i, a i * b i| ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

private theorem abs_weighted_contraction_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → ℝ) (F : ι → κ → ℝ) (T : κ → ℝ) :
    |∑ i, d i * ∑ j, F i j * T j| ≤
      Real.sqrt (∑ i, d i ^ 2) * Real.sqrt (∑ i, ∑ j, F i j ^ 2) *
        Real.sqrt (∑ j, T j ^ 2) := by
  have h := abs_sum_mul_le_sqrt_sq
    (fun p : ι × κ => F p.1 p.2) (fun p => d p.1 * T p.2)
  have hleft : (∑ p : ι × κ, F p.1 p.2 * (d p.1 * T p.2)) =
      ∑ i, d i * ∑ j, F i j * T j := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hright : (∑ p : ι × κ, (d p.1 * T p.2) ^ 2) =
      (∑ i, d i ^ 2) * (∑ j, T j ^ 2) := by
    simp only [Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hleft, hright,
    Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  simp only [Fintype.sum_prod_type] at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

namespace RiemannianMetric

theorem abs_tensorPairingTwo_le (g : RiemannianMetric n M)
    (S T : CovariantTensorEvaluation n M 2) (x : M) :
    |g.tensorPairingTwo S T x| ≤
      Real.sqrt (g.tensorPairingTwo S S x) * Real.sqrt (g.tensorPairingTwo T T x) := by
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  have h := abs_sum_mul_le_sqrt_sq
    (fun p : I × I => S x ![g.orthonormalBasis x p.1, g.orthonormalBasis x p.2])
    (fun p => T x ![g.orthonormalBasis x p.1, g.orthonormalBasis x p.2])
  simpa only [Fintype.sum_prod_type, tensorPairingTwo, pow_two] using h

theorem abs_tensorPairingThree_le (g : RiemannianMetric n M)
    (F G : CovariantTensorEvaluation n M 3) (x : M) :
    |g.tensorPairingThree F G x| ≤
      Real.sqrt (g.tensorPairingThree F F x) * Real.sqrt (g.tensorPairingThree G G x) := by
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  have h := abs_sum_mul_le_sqrt_sq
    (fun p : I × (I × I) => F x ![g.orthonormalBasis x p.1,
      g.orthonormalBasis x p.2.1, g.orthonormalBasis x p.2.2])
    (fun p => G x ![g.orthonormalBasis x p.1,
      g.orthonormalBasis x p.2.1, g.orthonormalBasis x p.2.2])
  simpa only [Fintype.sum_prod_type, tensorPairingThree, pow_two] using h

end RiemannianMetric

namespace LeviCivitaData

theorem abs_gradient_tensorPairingCovector_le (D : LeviCivitaData g)
    (φ : M → ℝ) (F : CovariantTensorEvaluation n M 3)
    (T : CovariantTensorEvaluation n M 2) (x : M) :
    |∑ a, mvfderiv (𝓡 n) φ x (g.orthonormalBasis x a) *
      g.tensorPairingCovector F T x ![g.orthonormalBasis x a]| ≤
      Real.sqrt (g.inner x (D.gradient φ x) (D.gradient φ x)) *
        Real.sqrt (g.tensorPairingThree F F x) * Real.sqrt (g.tensorPairingTwo T T x) := by
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  have h := abs_weighted_contraction_le
    (fun a : I => mvfderiv (𝓡 n) φ x (g.orthonormalBasis x a))
    (fun a (p : I × I) => F x ![g.orthonormalBasis x a,
      g.orthonormalBasis x p.1, g.orthonormalBasis x p.2])
    (fun p => T x ![g.orthonormalBasis x p.1, g.orthonormalBasis x p.2])
  rw [← D.gradient_normSq_eq_sum_mvfderiv_sq] at h
  simpa only [Fintype.sum_prod_type, RiemannianMetric.tensorPairingCovector,
    RiemannianMetric.tensorPairingThree, RiemannianMetric.tensorPairingTwo,
    Matrix.cons_val_zero, pow_two] using h

end LeviCivitaData
end PoincareConjecture
