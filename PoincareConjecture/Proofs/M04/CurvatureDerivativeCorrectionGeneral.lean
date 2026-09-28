import PoincareConjecture.Proofs.M04.TensorNormBounds
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem abs_ricci_basis_pair_le_general
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
    simp only [LeviCivitaData.riemannEvaluation,
      Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, hi, hp, hj, mul_one] at h
    have hnorm : g.tensorNorm D.riemannEvaluation x = N := by
      change D.curvatureDerivativeNorm 0 x = N
      exact D.curvatureDerivativeNorm_zero x
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
    _ ≤ ∑ _p : Fin d, N := Finset.sum_le_sum fun p _ ↦ hcomponent p
    _ = (n : ℝ) * N := by simp [hdim]

theorem inverse_metric_correction_le_general
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (m : ℕ) (x : M) :
    2 * (∑ j : Fin (4 + m),
      ∑ a : Fin (4 + m) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      ∑ l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.ricci x (g.orthonormalBasis x (a j))
            (g.orthonormalBasis x l) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (fun i ↦ g.orthonormalBasis x (a i)) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (fun i ↦ g.orthonormalBasis x (Function.update a j l i))) ≤
      2 * ((m + 4 : ℕ) : ℝ) * (n : ℝ) ^ (m + 6) *
        D.curvatureDerivativeNorm 0 x *
        (D.curvatureDerivativeNorm m x) ^ 2 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let N0 := D.curvatureDerivativeNorm 0 x
  let Nm := D.curvatureDerivativeNorm m x
  have hdim : d = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hN0 : 0 ≤ N0 := by
    dsimp [N0, LeviCivitaData.curvatureDerivativeNorm, RiemannianMetric.tensorNorm]
    exact Real.sqrt_nonneg _
  have hNm : 0 ≤ Nm := by
    dsimp [Nm, LeviCivitaData.curvatureDerivativeNorm, RiemannianMetric.tensorNorm]
    exact Real.sqrt_nonneg _
  have smoothIterated : ∀ q : ℕ,
      IsSmoothCovariantTensor
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation q) := by
    intro q
    induction q with
    | zero => exact isSmoothCovariantTensor_riemannEvaluation D
    | succ q ih => exact isSmoothCovariantTensor_covariantTensorDerivative D ih
  have hRic (j : Fin (4 + m)) (a : Fin (4 + m) → Fin d) (l : Fin d) :
      |D.ricci x (b (a j)) (b l)| ≤ (n : ℝ) * N0 := by
    dsimp [N0]
    rw [D.curvatureDerivativeNorm_zero x]
    simpa [b] using abs_ricci_basis_pair_le_general D x (a j) l
  have hTensor (a : Fin (4 + m) → Fin d) :
      |D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
        (fun i ↦ b (a i))| ≤ Nm := by
    have h := tensorEvaluation_sq_le_tensorNorm g
      (smoothIterated m)
      x (fun i ↦ b (a i))
    have hi (i : Fin (4 + m)) : g.inner x (b (a i)) (b (a i)) = 1 := by
      change inner ℝ (b (a i)) (b (a i)) = 1
      simp only [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
    simp only [hi, Finset.prod_const, Finset.card_univ,
      one_pow, mul_one] at h
    have hnorm : g.tensorNorm
        (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) x = Nm := by
      rfl
    rw [hnorm] at h
    have habs : |D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
        (fun i ↦ b (a i))| ^ 2 ≤ Nm ^ 2 := by
      simpa only [sq_abs] using h
    have habnon : 0 ≤ |D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
        (fun i ↦ b (a i))| := abs_nonneg _
    nlinarith [habs, habnon, hNm]
  have hTensorUpdate (j : Fin (4 + m)) (a : Fin (4 + m) → Fin d) (l : Fin d) :
      |D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
        (fun i ↦ b (Function.update a j l i))| ≤ Nm := by
    exact hTensor (Function.update a j l)
  have hterm (j : Fin (4 + m)) (a : Fin (4 + m) → Fin d) (l : Fin d) :
      D.ricci x (b (a j)) (b l) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (fun i ↦ b (a i)) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (fun i ↦ b (Function.update a j l i)) ≤
        (n : ℝ) * N0 * Nm ^ 2 := by
    calc
      _ ≤ |D.ricci x (b (a j)) (b l)| *
          |D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (fun i ↦ b (a i))| *
          |D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (fun i ↦ b (Function.update a j l i))| := by
        rw [← abs_mul, ← abs_mul]
        exact le_abs_self _
      _ ≤ (n : ℝ) * N0 * Nm ^ 2 := by
        have h0 := hRic j a l
        have h1 := hTensor a
        have h2 := hTensorUpdate j a l
        have hp0 : 0 ≤ (n : ℝ) * N0 := mul_nonneg (Nat.cast_nonneg n) hN0
        calc
          _ ≤ ((n : ℝ) * N0) * Nm * Nm := by
            exact mul_le_mul (mul_le_mul h0 h1 (abs_nonneg _) hp0) h2
              (abs_nonneg _) (mul_nonneg hp0 hNm)
          _ = (n : ℝ) * N0 * Nm ^ 2 := by ring_nf
  have hsum :
      (∑ j : Fin (4 + m), ∑ a : Fin (4 + m) → Fin d, ∑ l : Fin d,
        D.ricci x (b (a j)) (b l) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (fun i ↦ b (a i)) *
          D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
            (fun i ↦ b (Function.update a j l i))) ≤
      ((m + 4 : ℕ) : ℝ) * (n : ℝ) ^ (m + 6) * N0 * Nm ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin (4 + m), ∑ _a : Fin (4 + m) → Fin d, ∑ _l : Fin d,
          (n : ℝ) * N0 * Nm ^ 2 := by
        exact Finset.sum_le_sum fun j _ ↦
          Finset.sum_le_sum fun a _ ↦
            Finset.sum_le_sum fun l _ ↦ hterm j a l
      _ = ((m + 4 : ℕ) : ℝ) * (n : ℝ) ^ (m + 6) * N0 * Nm ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, hdim, Nat.cast_pow, nsmul_eq_mul]
        ring
  dsimp only [b, d, N0, Nm] at hsum ⊢
  nlinarith

end PoincareConjecture.M04
