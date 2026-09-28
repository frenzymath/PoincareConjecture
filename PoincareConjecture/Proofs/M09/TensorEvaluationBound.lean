import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators RealInnerProductSpace

universe u

namespace PoincareConjecture.Proofs.M09

theorem multilinear_abs_le_componentNorm
    {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype K]
    {k : ℕ} (A : MultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ)
    (b : OrthonormalBasis K ℝ E) (v : Fin k → E) :
    |A v| ≤ Real.sqrt (∑ a : Fin k → K, (A (fun i ↦ b (a i))) ^ 2) *
      ∏ i, ‖v i‖ := by
  classical
  have hexpand : A v = ∑ a : Fin k → K,
      (∏ i, ⟪b (a i), v i⟫) * A (fun i ↦ b (a i)) := by
    calc
      A v = A (fun i ↦ ∑ j, ⟪b j, v i⟫ • b j) := by
        congr 1
        funext i
        exact (b.sum_repr' (v i)).symm
      _ = _ := by
        rw [A.map_sum]
        simp_rw [A.map_smul_univ, smul_eq_mul]
  have hcoeff : (∑ a : Fin k → K, (∏ i, ⟪b (a i), v i⟫) ^ 2) =
      (∏ i, ‖v i‖) ^ 2 := by
    simp_rw [← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun (i : Fin k) (j : K) ↦ ⟪b j, v i⟫ ^ 2)]
    simp_rw [b.sum_sq_inner_right]
  rw [hexpand]
  calc
    _ ≤ ∑ a : Fin k → K,
        |(∏ i, ⟪b (a i), v i⟫) * A (fun i ↦ b (a i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Fin k → K,
        |∏ i, ⟪b (a i), v i⟫| * |A (fun i ↦ b (a i))| := by
      simp_rw [abs_mul]
    _ ≤ Real.sqrt (∑ a : Fin k → K, (∏ i, ⟪b (a i), v i⟫) ^ 2) *
        Real.sqrt (∑ a : Fin k → K, (A (fun i ↦ b (a i))) ^ 2) := by
      simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun a : Fin k → K ↦ |∏ i, ⟪b (a i), v i⟫|)
        (fun a : Fin k → K ↦ |A (fun i ↦ b (a i))|)
    _ = _ := by
      rw [hcoeff, Real.sqrt_sq (Finset.prod_nonneg fun i _ ↦ norm_nonneg (v i)), mul_comm]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem tensor_abs_le_tensorNorm (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    |T x v| ≤ g.tensorNorm T x * ∏ i, g.tangentNorm x (v i) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hT.1 x
  have hn (w : TangentSpace (𝓡 n) x) : ‖w‖ = g.tangentNorm x w := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have h := multilinear_abs_le_componentNorm A (g.orthonormalBasis x) v
  simpa only [RiemannianMetric.tensorNorm, ← hA, hn] using h

theorem ricci_abs_le_curvatureTensorNorm (hM04 : RicciFlowCurvatureTheory.{u})
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    |D.ricci x v w| ≤ (n : ℝ) * D.curvatureTensorNorm x *
      g.tangentNorm x v * g.tangentNorm x w := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.tangentNorm x (b i) = 1 := by
    change Real.sqrt ⟪b i, b i⟫ = 1
    rw [← norm_eq_sqrt_real_inner, b.norm_eq_one]
  have hnorm : g.tensorNorm D.riemannEvaluation x = D.curvatureTensorNorm x :=
    hM04.curvature_norm_zero n M g D x
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      |D.curvatureTensor x v (b i) w (b i)| ≤
        D.curvatureTensorNorm x * g.tangentNorm x v * g.tangentNorm x w := by
    have h := tensor_abs_le_tensorNorm g D.riemannEvaluation
      (hM04.tensor_calculus n M g D).1 x ![v, b i, w, b i]
    simpa [LeviCivitaData.riemannEvaluation, hnorm, Fin.prod_univ_succ, hb, mul_assoc]
      using h
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    _ ≤ ∑ i, |D.curvatureTensor x v (b i) w (b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.curvatureTensorNorm x * g.tangentNorm x v * g.tangentNorm x w :=
      Finset.sum_le_sum fun i _ ↦ hterm i
    _ = _ := by simp [hdim, mul_assoc]

theorem scalar_abs_le_curvatureTensorNorm (hM04 : RicciFlowCurvatureTheory.{u})
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M) :
    |D.scalarCurvature x| ≤ (n : ℝ) ^ 2 * D.curvatureTensorNorm x := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.tangentNorm x (b i) = 1 := by
    change Real.sqrt ⟪b i, b i⟫ = 1
    rw [← norm_eq_sqrt_real_inner, b.norm_eq_one]
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      |D.ricci x (b i) (b i)| ≤ (n : ℝ) * D.curvatureTensorNorm x := by
    simpa only [hb, mul_one] using ricci_abs_le_curvatureTensorNorm hM04 g D x (b i) (b i)
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    _ ≤ ∑ i, |D.ricci x (b i) (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (n : ℝ) * D.curvatureTensorNorm x := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = _ := by simp [hdim, pow_two, mul_assoc]

end PoincareConjecture.Proofs.M09
