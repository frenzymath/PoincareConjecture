import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Diagonal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MetricDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Manifold ContDiff Bundle
open Matrix

namespace Poincare.RicciFlow.Harnack

variable {I J : Type*} [Fintype I] [Fintype J]

lemma hamiltonBlock_posSemidef_change_coordinates
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ) (M : I → I → ℝ)
    (C : J → I → ℝ)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef) :
    (Matrix.fromBlocks
      (fun ac bd : J × J => ∑ a, ∑ b, ∑ c, ∑ d,
        C ac.1 a * C ac.2 b * R a b c d * C bd.1 c * C bd.2 d)
      (fun (ac : J × J) d => ∑ a, ∑ b, ∑ c,
        C ac.1 a * C ac.2 b * P a b c * C d c)
      (fun c (bd : J × J) => ∑ a, ∑ b, ∑ d,
        C bd.1 a * C bd.2 b * P a b d * C c d)
      (fun a b => ∑ c, ∑ d, C a c * M c d * C b d)).PosSemidef := by
  classical
  let B : Matrix ((J × J) ⊕ J) ((I × I) ⊕ I) ℝ :=
    Matrix.fromBlocks (fun ab cd => C ab.1 cd.1 * C ab.2 cd.2) 0 0 C
  have h := hQ.mul_mul_conjTranspose_same B
  have hsum (f : I → I → I → I → ℝ) :
      (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro c _
    exact Finset.sum_comm_cycle
  convert h using 1
  ext (ab | a) (cd | c)
  · simp only [Matrix.mul_apply, B, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.conjTranspose_apply, star_trivial, Matrix.zero_apply,
      zero_mul, mul_zero, Finset.sum_const_zero, add_zero, Finset.sum_mul]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  · simp only [Matrix.mul_apply, B, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.conjTranspose_apply, star_trivial, Matrix.zero_apply,
      zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      Finset.sum_mul]
    rw [Finset.sum_comm_cycle]
  · simp only [Matrix.mul_apply, B, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.conjTranspose_apply, star_trivial, Matrix.zero_apply,
      zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp only [Matrix.mul_apply, B, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.conjTranspose_apply, star_trivial, Matrix.zero_apply,
      zero_mul, mul_zero, Finset.sum_const_zero, zero_add, Finset.sum_mul]
    rw [Finset.sum_comm]

open PoincareConjecture

universe u

variable {n : ℕ} {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

lemma tensor_two_expansion (g : RiemannianMetric n N)
    {T : CovariantTensorEvaluation n N 2} (hT : IsSmoothCovariantTensor T)
    (x : N) (u v : TangentSpace (𝓡 n) x) :
    T x ![u, v] = ∑ a, ∑ b, g.inner x u (g.orthonormalBasis x a) *
      T x ![g.orthonormalBasis x a, g.orthonormalBasis x b] *
        g.inner x v (g.orthonormalBasis x b) := by
  have h₀ : T x ![u, v] = ∑ a, g.inner x u (g.orthonormalBasis x a) *
      T x ![g.orthonormalBasis x a, v] := by
    have he (q) : Function.update ![u, v] 0 q = ![q, v] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![u, v] 0 u
  have h₁ (w) : T x ![w, v] = ∑ b, g.inner x v (g.orthonormalBasis x b) *
      T x ![w, g.orthonormalBasis x b] := by
    have he (q) : Function.update ![w, v] 1 q = ![w, q] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![w, v] 1 v
  rw [h₀]
  simp_rw [h₁, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma tensor_three_expansion (g : RiemannianMetric n N)
    {T : CovariantTensorEvaluation n N 3} (hT : IsSmoothCovariantTensor T)
    (x : N) (u v w : TangentSpace (𝓡 n) x) :
    T x ![u, v, w] = ∑ a, ∑ b, ∑ c,
      g.inner x u (g.orthonormalBasis x a) * g.inner x v (g.orthonormalBasis x b) *
        T x ![g.orthonormalBasis x a, g.orthonormalBasis x b, g.orthonormalBasis x c] *
          g.inner x w (g.orthonormalBasis x c) := by
  have h₀ : T x ![u, v, w] = ∑ a, g.inner x u (g.orthonormalBasis x a) *
      T x ![g.orthonormalBasis x a, v, w] := by
    have he (q) : Function.update ![u, v, w] 0 q = ![q, v, w] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![u, v, w] 0 u
  have h₁ (q) : T x ![q, v, w] = ∑ b, g.inner x v (g.orthonormalBasis x b) *
      T x ![q, g.orthonormalBasis x b, w] := by
    have he (r) : Function.update ![q, v, w] 1 r = ![q, r, w] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![q, v, w] 1 v
  have h₂ (q r) : T x ![q, r, w] = ∑ c, g.inner x w (g.orthonormalBasis x c) *
      T x ![q, r, g.orthonormalBasis x c] := by
    have he (s) : Function.update ![q, r, w] 2 s = ![q, r, s] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![q, r, w] 2 w
  rw [h₀]
  simp_rw [h₁, h₂, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma tensor_four_expansion (g : RiemannianMetric n N)
    {T : CovariantTensorEvaluation n N 4} (hT : IsSmoothCovariantTensor T)
    (x : N) (u v w z : TangentSpace (𝓡 n) x) :
    T x ![u, v, w, z] = ∑ a, ∑ b, ∑ c, ∑ d,
      g.inner x u (g.orthonormalBasis x a) * g.inner x v (g.orthonormalBasis x b) *
        T x ![g.orthonormalBasis x a, g.orthonormalBasis x b,
          g.orthonormalBasis x c, g.orthonormalBasis x d] *
          g.inner x w (g.orthonormalBasis x c) * g.inner x z (g.orthonormalBasis x d) := by
  have h₀ : T x ![u, v, w, z] = ∑ a, g.inner x u (g.orthonormalBasis x a) *
      T x ![g.orthonormalBasis x a, v, w, z] := by
    have he (q) : Function.update ![u, v, w, z] 0 q = ![q, v, w, z] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![u, v, w, z] 0 u
  have h₁ (q) : T x ![q, v, w, z] = ∑ b, g.inner x v (g.orthonormalBasis x b) *
      T x ![q, g.orthonormalBasis x b, w, z] := by
    have he (r) : Function.update ![q, v, w, z] 1 r = ![q, r, w, z] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![q, v, w, z] 1 v
  have h₂ (q r) : T x ![q, r, w, z] = ∑ c, g.inner x w (g.orthonormalBasis x c) *
      T x ![q, r, g.orthonormalBasis x c, z] := by
    have he (s) : Function.update ![q, r, w, z] 2 s = ![q, r, s, z] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![q, r, w, z] 2 w
  have h₃ (q r s) : T x ![q, r, s, z] = ∑ d, g.inner x z (g.orthonormalBasis x d) *
      T x ![q, r, s, g.orthonormalBasis x d] := by
    have he (t) : Function.update ![q, r, s, z] 3 t = ![q, r, s, t] := by
      ext i; fin_cases i <;> simp [Function.update]
    simpa only [he] using hT.update_eq_sum g x ![q, r, s, z] 3 z
  rw [h₀]
  simp_rw [h₁, h₂, h₃, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem tensor_block_posSemidef_of_basis
    (g : RiemannianMetric n N)
    {R : CovariantTensorEvaluation n N 4} {P : CovariantTensorEvaluation n N 3}
    {B : CovariantTensorEvaluation n N 2}
    (hR : IsSmoothCovariantTensor R) (hP : IsSmoothCovariantTensor P)
    (hB : IsSmoothCovariantTensor B) (x : N)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        R x ![g.orthonormalBasis x ac.1, g.orthonormalBasis x ac.2,
        g.orthonormalBasis x bd.1, g.orthonormalBasis x bd.2])
      (fun ac d => P x ![g.orthonormalBasis x ac.1, g.orthonormalBasis x ac.2,
        g.orthonormalBasis x d])
      (fun c bd => P x ![g.orthonormalBasis x bd.1, g.orthonormalBasis x bd.2,
        g.orthonormalBasis x c])
      (fun a b => B x ![g.orthonormalBasis x a, g.orthonormalBasis x b])).PosSemidef)
    (e : J → TangentSpace (𝓡 n) x) :
    (Matrix.fromBlocks (fun ac bd : J × J => R x ![e ac.1, e ac.2, e bd.1, e bd.2])
      (fun ac d => P x ![e ac.1, e ac.2, e d])
      (fun c bd => P x ![e bd.1, e bd.2, e c])
      (fun a b => B x ![e a, e b])).PosSemidef := by
  have h := hamiltonBlock_posSemidef_change_coordinates
    (fun a b c d => R x ![g.orthonormalBasis x a, g.orthonormalBasis x b,
      g.orthonormalBasis x c, g.orthonormalBasis x d])
    (fun a b c => P x ![g.orthonormalBasis x a, g.orthonormalBasis x b,
      g.orthonormalBasis x c])
    (fun a b => B x ![g.orthonormalBasis x a, g.orthonormalBasis x b])
    (fun a b => g.inner x (e a) (g.orthonormalBasis x b)) hQ
  simpa only [← tensor_two_expansion g hB, ← tensor_three_expansion g hP,
    ← tensor_four_expansion g hR] using h

end Poincare.RicciFlow.Harnack
