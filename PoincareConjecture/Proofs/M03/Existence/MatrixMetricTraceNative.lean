import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Basis

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators Matrix

noncomputable section

namespace PoincareConjecture.DeTurckNative

variable {V F ι κ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem sum_orthonormal_coordinates_eq_inverse_gram
    (e : OrthonormalBasis κ ℝ V) (b : Module.Basis ι ℝ V) (i j : ι) :
    (∑ r, b.repr (e r) i * b.repr (e r) j) = (Matrix.gram ℝ b)⁻¹ i j := by
  let C : Matrix κ ι ℝ := e.toBasis.toMatrix b
  let D : Matrix ι κ ℝ := b.toMatrix e.toBasis
  have hCD : C * D = 1 := e.toBasis.toMatrix_mul_toMatrix_flip b
  have hDC : D * C = 1 := b.toMatrix_mul_toMatrix_flip e.toBasis
  have hC : (Matrix.of fun r a => e.repr (b a) r) = C := by
    ext r a
    simp only [Matrix.of_apply, C, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply]
  have hG : Matrix.gram ℝ b = Cᵀ * C := by
    simpa only [hC, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.gram_eq_conjTranspose_mul e b)
  have hleft : (D * Dᵀ) * Matrix.gram ℝ b = 1 := by
    calc
      (D * Dᵀ) * Matrix.gram ℝ b = (D * Dᵀ) * (Cᵀ * C) := by rw [hG]
      _ = D * (Dᵀ * Cᵀ) * C := by simp only [Matrix.mul_assoc]
      _ = D * (C * D)ᵀ * C := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hCD, Matrix.transpose_one, Matrix.mul_one, hDC]
  have hinv : (Matrix.gram ℝ b)⁻¹ = D * Dᵀ := Matrix.inv_eq_left_inv hleft
  have hentry := congrArg (fun A : Matrix ι ι ℝ => A i j) hinv
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, D, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis] using hentry.symm

theorem orthonormal_trace_eq_inverse_gram
    (e : OrthonormalBasis κ ℝ V) (b : Module.Basis ι ℝ V)
    (A : V →L[ℝ] V →L[ℝ] F) :
    (∑ r, A (e r) (e r)) =
      ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j • A (b i) (b j) := by
  have hexpand (v w : V) :
      A v w = ∑ i, ∑ j, (b.repr v i * b.repr w j) • A (b i) (b j) := by
    calc
      A v w = A (∑ i, b.repr v i • b i) (∑ j, b.repr w j • b j) := by
        rw [b.sum_repr, b.sum_repr]
      _ = _ := by
        simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
          ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp only [mul_comm]
  calc
    (∑ r, A (e r) (e r)) =
        ∑ r, ∑ i, ∑ j, (b.repr (e r) i * b.repr (e r) j) • A (b i) (b j) := by
      exact Finset.sum_congr rfl fun r _ => hexpand (e r) (e r)
    _ = ∑ i, ∑ j, (∑ r, b.repr (e r) i * b.repr (e r) j) • A (b i) (b j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_smul.symm
    _ = _ := by
      simp only [sum_orthonormal_coordinates_eq_inverse_gram e b]

end PoincareConjecture.DeTurckNative

end
