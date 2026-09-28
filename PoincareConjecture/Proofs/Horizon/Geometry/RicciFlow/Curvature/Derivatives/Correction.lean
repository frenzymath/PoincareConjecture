import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeClosure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset





set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem abs_ricci_basis_pair_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    |D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j)| ≤
      (n : ℝ) * D.curvatureTensorNorm x := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let N := D.curvatureTensorNorm x
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hdim : d = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hcomponent (p : Fin d) :
      |D.curvatureTensor x (b i) (b p) (b j) (b p)| ≤ N := by
    have h := tensorEvaluation_sq_le_tensorNorm g
      (isSmoothCovariantTensor_riemannEvaluation D) x
      ![b i, b p, b j, b p]
    have hi : g.inner x (b i) (b i) = 1 := by
      change inner ℝ (b i) (b i) = 1
      simp only [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
    have hp : g.inner x (b p) (b p) = 1 := by
      change inner ℝ (b p) (b p) = 1
      simp only [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
    have hj : g.inner x (b j) (b j) = 1 := by
      change inner ℝ (b j) (b j) = 1
      simp only [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
    simp only [LeviCivitaData.riemannEvaluation, D.horizon_curvatureDerivativeNorm_zero,
      Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, hi, hp, hj, mul_one] at h
    have hnorm : g.tensorNorm D.riemannEvaluation x = N := by
      change D.curvatureDerivativeNorm 0 x = N
      exact D.horizon_curvatureDerivativeNorm_zero x
    rw [hnorm] at h
    have habs : |D.curvatureTensor x (b i) (b p) (b j) (b p)| ^ 2 ≤ N ^ 2 := by
      simpa only [sq_abs] using h
    nlinarith only [habs,
      abs_nonneg (D.curvatureTensor x (b i) (b p) (b j) (b p)), hN]
  change |∑ p : Fin d,
    D.curvatureTensor x (b i) (b p) (b j) (b p)| ≤ _
  calc
    _ ≤ ∑ p : Fin d, |D.curvatureTensor x (b i) (b p) (b j) (b p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin d, N := Finset.sum_le_sum fun p _ => hcomponent p
    _ = (n : ℝ) * N := by simp [hdim]

theorem inverse_metric_correction_le
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) :
    2 * (∑ j : Fin 5,
      ∑ a : Fin 5 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      ∑ l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.ricci x (g.orthonormalBasis x (a j))
            (g.orthonormalBasis x l) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
            (fun i ↦ g.orthonormalBasis x (a i)) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
            (fun i ↦ g.orthonormalBasis x (Function.update a j l i))) ≤
      10 * (n : ℝ) ^ 7 * D.curvatureDerivativeNorm 0 x *
        (D.curvatureDerivativeNorm 1 x) ^ 2 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let N0 := D.curvatureDerivativeNorm 0 x
  let N1 := D.curvatureDerivativeNorm 1 x
  have hdim : d = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hN0 : 0 ≤ N0 := by
    dsimp [N0, LeviCivitaData.curvatureDerivativeNorm, RiemannianMetric.tensorNorm]
    exact Real.sqrt_nonneg _
  have hN1 : 0 ≤ N1 := by
    dsimp [N1, LeviCivitaData.curvatureDerivativeNorm, RiemannianMetric.tensorNorm]
    exact Real.sqrt_nonneg _
  have hRic (j : Fin 5) (a : Fin 5 → Fin d) (l : Fin d) :
      |D.ricci x (b (a j)) (b l)| ≤ (n : ℝ) * N0 := by
    dsimp [N0]
    rw [D.horizon_curvatureDerivativeNorm_zero x]
    simpa [b] using abs_ricci_basis_pair_le D x (a j) l
  have hTensor (a : Fin 5 → Fin d) :
      |D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
        (fun i ↦ b (a i))| ≤ N1 := by
    change |D.covariantTensorDerivative D.riemannEvaluation x
      (fun i ↦ b (a i))| ≤ N1
    have h := tensorEvaluation_sq_le_tensorNorm g
      (isSmoothCovariantTensor_covariantTensorDerivative D
        (isSmoothCovariantTensor_riemannEvaluation D)) x
      (fun i ↦ b (a i))
    have hi (i : Fin 5) : g.inner x (b (a i)) (b (a i)) = 1 := by
      change inner ℝ (b (a i)) (b (a i)) = 1
      simp only [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
    simp only [Fin.prod_univ_succ, hi, Finset.prod_const, Finset.card_univ,
      one_pow, one_mul, mul_one] at h
    have hnorm1 : g.tensorNorm (D.covariantTensorDerivative D.riemannEvaluation) x = N1 := by
      rfl
    rw [hnorm1] at h
    have habs : |D.covariantTensorDerivative D.riemannEvaluation x
        (fun i ↦ b (a i))| ^ 2 ≤ N1 ^ 2 := by
      simpa only [sq_abs] using h
    have habnon : 0 ≤ |D.covariantTensorDerivative D.riemannEvaluation x
        (fun i ↦ b (a i))| := abs_nonneg _
    nlinarith [habs, habnon, hN1]
  have hTensorUpdate (j : Fin 5) (a : Fin 5 → Fin d) (l : Fin d) :
      |D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
        (fun i ↦ b (Function.update a j l i))| ≤ N1 := by
    exact hTensor (Function.update a j l)
  have hterm (j : Fin 5) (a : Fin 5 → Fin d) (l : Fin d) :
      D.ricci x (b (a j)) (b l) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
            (fun i ↦ b (a i)) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
            (fun i ↦ b (Function.update a j l i)) ≤
        (n : ℝ) * N0 * N1 ^ 2 := by
    calc
      _ ≤ |D.ricci x (b (a j)) (b l)| *
          |D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
            (fun i ↦ b (a i))| *
          |D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
            (fun i ↦ b (Function.update a j l i))| := by
        rw [← abs_mul, ← abs_mul]
        exact le_abs_self _
      _ ≤ (n : ℝ) * N0 * N1 ^ 2 := by
        have h0 := hRic j a l
        have h1 := hTensor a
        have h2 := hTensorUpdate j a l
        have hp0 : 0 ≤ (n : ℝ) * N0 := mul_nonneg (Nat.cast_nonneg n) hN0
        calc
          _ ≤ ((n : ℝ) * N0) * N1 * N1 := by
            exact mul_le_mul (mul_le_mul h0 h1 (abs_nonneg _) hp0) h2
              (abs_nonneg _) (mul_nonneg hp0 hN1)
          _ = (n : ℝ) * N0 * N1 ^ 2 := by ring
  have hsum :
      (∑ j : Fin 5, ∑ a : Fin 5 → Fin d, ∑ l : Fin d,
        D.ricci x (b (a j)) (b l) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
            (fun i ↦ b (a i)) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation 1 x
            (fun i ↦ b (Function.update a j l i))) ≤
      5 * (n : ℝ) ^ 7 * N0 * N1 ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin 5, ∑ _a : Fin 5 → Fin d, ∑ _l : Fin d,
          (n : ℝ) * N0 * N1 ^ 2 := by
        exact Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun a _ =>
            Finset.sum_le_sum fun l _ => hterm j a l
      _ = 5 * (n : ℝ) ^ 7 * N0 * N1 ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          hdim, Nat.cast_pow, nsmul_eq_mul]
        ring
  dsimp only [b, d, N0, N1] at hsum ⊢
  nlinarith

end PoincareConjecture.RicciFlowAnalysis
