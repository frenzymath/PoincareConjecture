import PoincareConjecture.Proofs.M04.RiemannRegularity
import PoincareConjecture.Proofs.M04.TensorNorm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem tensorEvaluation_sq_le_tensorNorm (g : RiemannianMetric n M) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    (T x v) ^ 2 ≤ (g.tensorNorm T x) ^ 2 * ∏ i, g.inner x (v i) (v i) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  obtain ⟨A, hA⟩ := hT.1 x
  have hExpand : T x v = ∑ a : Fin k → Fin d,
      (∏ i, b.repr (v i) (a i)) * T x (fun i ↦ b (a i)) := by
    rw [hA v]
    calc
      A v = A (fun i ↦ ∑ j, b.repr (v i) j • b j) := by
        simp only [b.sum_repr]
      _ = ∑ a : Fin k → Fin d, A (fun i ↦ b.repr (v i) (a i) • b (a i)) :=
        A.map_sum _
      _ = _ := by simp only [A.map_smul_univ, smul_eq_mul, hA]
  have hParseval (z : TangentSpace (𝓡 n) x) :
      ∑ j, (b.repr z j) ^ 2 = g.inner x z z := by
    calc
      _ = ∑ j, ‖inner ℝ (b j) z‖ ^ 2 := by
        simp only [b.repr_apply_apply, Real.norm_eq_abs, sq_abs]
      _ = ‖z‖ ^ 2 := b.sum_sq_norm_inner_right z
      _ = _ := (real_inner_self_eq_norm_sq z).symm
  have hCoeff : (∑ a : Fin k → Fin d, (∏ i, b.repr (v i) (a i)) ^ 2) =
      ∏ i, g.inner x (v i) (v i) := by
    simp_rw [← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun (i : Fin k) (j : Fin d) ↦ (b.repr (v i) j) ^ 2)]
    exact Finset.prod_congr rfl (fun i _ ↦ hParseval (v i))
  have hNorm : (∑ a : Fin k → Fin d, (T x (fun i ↦ b (a i))) ^ 2) =
      (g.tensorNorm T x) ^ 2 := by
    symm
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  rw [hExpand]
  calc
    _ ≤ (∑ a : Fin k → Fin d, (∏ i, b.repr (v i) (a i)) ^ 2) *
        ∑ a : Fin k → Fin d, (T x (fun i ↦ b (a i))) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by rw [hCoeff, hNorm, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem abs_ricci_le_curvatureTensorNorm {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 n) x) :
    |D.ricci x v v| ≤ (n : ℝ) * D.curvatureTensorNorm x * g.inner x v v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hNorm : g.tensorNorm D.riemannEvaluation x = D.curvatureTensorNorm x :=
    D.curvatureDerivativeNorm_zero x
  have hN : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  have hV : 0 ≤ g.inner x v v := real_inner_self_nonneg (x := v)
  have hTerm (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      |D.curvatureTensor x v (b i) v (b i)| ≤ D.curvatureTensorNorm x * g.inner x v v := by
    have h := tensorEvaluation_sq_le_tensorNorm g
      (isSmoothCovariantTensor_riemannEvaluation D) x ![v, b i, v, b i]
    have hb : g.inner x (b i) (b i) = 1 := by
      change inner ℝ (b i) (b i) = 1
      simp only [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
    simp only [LeviCivitaData.riemannEvaluation, hNorm, Fin.prod_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hb, mul_one] at h
    have hNV := mul_nonneg hN hV
    have hAbs : |D.curvatureTensor x v (b i) v (b i)| ^ 2 ≤
        (D.curvatureTensorNorm x * g.inner x v v) ^ 2 := by
      rw [sq_abs]
      nlinarith only [h]
    nlinarith only [hAbs, abs_nonneg (D.curvatureTensor x v (b i) v (b i)), hNV]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    _ ≤ ∑ i, |D.curvatureTensor x v (b i) v (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.curvatureTensorNorm x * g.inner x v v := Finset.sum_le_sum fun i _ ↦ hTerm i
    _ = _ := by simp [hdim, mul_assoc]

end PoincareConjecture.M04
