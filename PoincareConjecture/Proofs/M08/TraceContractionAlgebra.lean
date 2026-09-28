import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators Matrix Classical

namespace PoincareConjecture.M08

variable {V ι κ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fintype ι] [Fintype κ]

theorem orthonormal_repr_sum_mul (e : Module.Basis ι ℝ V)
    (b : OrthonormalBasis κ ℝ V) (i j : ι) :
    ∑ a, e.repr (b a) i * e.repr (b a) j = (Matrix.gram ℝ e)⁻¹ i j := by
  classical
  let A : Matrix ι κ ℝ := e.toMatrix b.toBasis
  let B : Matrix κ ι ℝ := b.toBasis.toMatrix e
  have hAB : A * B = 1 := e.toMatrix_mul_toMatrix_flip b.toBasis
  have hBA : B * A = 1 := b.toBasis.toMatrix_mul_toMatrix_flip e
  have hG : Matrix.gram ℝ e = B.transpose * B := by
    have hB : (Matrix.of fun a i ↦ b.repr (e i) a) = B := by
      ext a i
      simp only [B, Matrix.of_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply]
    simpa only [hB, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.gram_eq_conjTranspose_mul b e
  have hInv : (Matrix.gram ℝ e)⁻¹ = A * A.transpose := by
    apply Matrix.inv_eq_left_inv
    rw [hG]
    calc
      A * A.transpose * (B.transpose * B) =
          A * (A.transpose * B.transpose) * B := by simp only [Matrix.mul_assoc]
      _ = A * (B * A).transpose * B := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hBA, Matrix.transpose_one, Matrix.mul_one, hAB]
  rw [hInv]
  rfl

theorem bilinear_trace_eq_inverseGram (e : Module.Basis ι ℝ V)
    (b : OrthonormalBasis κ ℝ V) (L : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∑ a, L (b a) (b a) =
      ∑ i, ∑ j, (Matrix.gram ℝ e)⁻¹ i j * L (e i) (e j) := by
  classical
  have hL (v w : V) : L v w =
      ∑ i, ∑ j, (e.repr v i * e.repr w j) * L (e i) (e j) := by
    calc
      L v w = L (∑ i, e.repr v i • e i) (∑ j, e.repr w j • e j) := by
        rw [e.sum_repr, e.sum_repr]
      _ = _ := by
        rw [map_sum]
        simp only [LinearMap.sum_apply, map_sum, map_smul, LinearMap.smul_apply,
          smul_eq_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  calc
    (∑ a, L (b a) (b a)) =
        ∑ a, ∑ i, ∑ j, (e.repr (b a) i * e.repr (b a) j) * L (e i) (e j) :=
      Finset.sum_congr rfl fun a _ ↦ hL (b a) (b a)
    _ = _ := ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, orthonormal_repr_sum_mul e b i j]

private def tensorPair02 (A : MultilinearMap ℝ (fun _ : Fin 4 ↦ V) ℝ) (v z : V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u w ↦ A ![u, v, w, z])
    (fun u₁ u₂ w ↦ by simpa only [Matrix.vecCons] using A.cons_add ![v, w, z] u₁ u₂)
    (fun a u w ↦ by simpa only [Matrix.vecCons] using A.cons_smul ![v, w, z] a u)
    (fun u w₁ w₂ ↦ by
      simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
        ((A.curryLeft u).curryLeft v).cons_add ![z] w₁ w₂)
    (fun a u w ↦ by
      simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
        ((A.curryLeft u).curryLeft v).cons_smul ![z] a w)

private def tensorPair13 (A : MultilinearMap ℝ (fun _ : Fin 4 ↦ V) ℝ) (u w : V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v z ↦ A ![u, v, w, z])
    (fun v₁ v₂ z ↦ by
      simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
        (A.curryLeft u).cons_add ![w, z] v₁ v₂)
    (fun a v z ↦ by
      simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
        (A.curryLeft u).cons_smul ![w, z] a v)
    (fun v z₁ z₂ ↦ by
      simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
        (((A.curryLeft u).curryLeft v).curryLeft w).cons_add ![] z₁ z₂)
    (fun a v z ↦ by
      simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
        (((A.curryLeft u).curryLeft v).curryLeft w).cons_smul ![] a z)

theorem fourTensor_trace_eq_inverseGram (e : Module.Basis ι ℝ V)
    (b : OrthonormalBasis κ ℝ V) (A : MultilinearMap ℝ (fun _ : Fin 4 ↦ V) ℝ) :
    (∑ a, ∑ c, A ![b a, b c, b a, b c]) =
      ∑ i, ∑ j, ∑ k, ∑ l, (Matrix.gram ℝ e)⁻¹ i j * (Matrix.gram ℝ e)⁻¹ k l *
        A ![e i, e k, e j, e l] := by
  classical
  have h02 (v : V) : (∑ a, A ![b a, v, b a, v]) =
      ∑ i, ∑ j, (Matrix.gram ℝ e)⁻¹ i j * A ![e i, v, e j, v] :=
    bilinear_trace_eq_inverseGram e b (tensorPair02 A v v)
  have h13 (u w : V) : (∑ c, A ![u, b c, w, b c]) =
      ∑ k, ∑ l, (Matrix.gram ℝ e)⁻¹ k l * A ![u, e k, w, e l] :=
    bilinear_trace_eq_inverseGram e b (tensorPair13 A u w)
  rw [Finset.sum_comm]
  simp_rw [h02]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, h13]
  simp only [Finset.mul_sum, mul_assoc]

end PoincareConjecture.M08
