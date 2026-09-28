import PoincareConjecture.Definitions.Ch04.Harnack
import PoincareConjecture.Definitions.Ch01.TensorOperators
import PoincareConjecture.Statements.Ch01.CurvatureCalculus
import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.Sectional
import PoincareConjecture.Proofs.M05.LinearAlgebra.CrossProduct.Orthonormal










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators Matrix

namespace PoincareConjecture.M35

open Poincare.Geometry.Curvature.Operator

private theorem skew_pair_sum (A B : Fin 3 → Fin 3 → ℝ)
    (hA : ∀ i j, A i j = -A j i) (hB : ∀ i j, B i j = -B j i) :
    (∑ i, ∑ j, A i j * B i j) =
      2 * ∑ a, A (pairFirst a) (pairSecond a) * B (pairFirst a) (pairSecond a) := by
  have hdiag (i) : A i i = 0 := by linarith [hA i i]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, pairFirst, pairSecond,
    Matrix.cons_val_zero, Matrix.cons_val_succ, hdiag, zero_mul, zero_add, add_zero]
  norm_num
  rw [hA 1 0, hA 0 2, hA 2 1, hB 1 0, hB 0 2, hB 2 1]
  ring

private theorem skew_curvature_contraction
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (A : Fin 3 → Fin 3 → ℝ) (hA : ∀ i j, A i j = -A j i) :
    (∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l) =
      4 * inner ℝ (WithLp.toLp 2 (fun a => A (pairFirst a) (pairSecond a)))
        (curvatureOperator R (WithLp.toLp 2 (fun a => A (pairFirst a) (pairSecond a)))) := by
  have hb (i j) : (∑ k, ∑ l, A k l * R i j k l) =
      -(∑ k, ∑ l, A k l * R j i k l) := by
    simp_rw [hfirst i j, mul_neg, Finset.sum_neg_distrib]
  calc
    _ = ∑ i, ∑ j, A i j * (∑ k, ∑ l, A k l * R i j k l) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = 2 * ∑ a, A (pairFirst a) (pairSecond a) *
        (∑ k, ∑ l, A k l * R (pairFirst a) (pairSecond a) k l) :=
      skew_pair_sum A _ hA hb
    _ = _ := by
      simp_rw [skew_pair_sum A _ hA (hlast _ _)]
      rw [curvatureOperator_rayleigh]
      simp only [dotProduct, Matrix.mulVec, curvatureMatrix, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem three_frame_operator_nonneg
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : MultilinearMap ℝ (fun _ : Fin 4 => V) ℝ) (b : Fin 3 → V)
    (hfirst : ∀ u v w z, T ![u, v, w, z] = -T ![v, u, w, z])
    (hlast : ∀ u v w z, T ![u, v, w, z] = -T ![u, v, z, w])
    (hplane : ∀ u v, 0 ≤ T ![u, v, u, v])
    (A : Fin 3 → Fin 3 → ℝ) (hA : ∀ i j, A i j = -A j i) :
    0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * T ![b i, b j, b k, b l] := by
  let R := fun i j k l => T ![b i, b j, b k, b l]
  have hRf (i j k l) : R i j k l = -R j i k l := hfirst _ _ _ _
  have hRl (i j k l) : R i j k l = -R i j l k := hlast _ _ _ _
  have hunit (w : EuclideanSpace ℝ (Fin 3)) (hw : ‖w‖ = 1) :
      0 ≤ inner ℝ w (curvatureOperator R w) := by
    obtain ⟨u, v, _hu, _hv, _huv, hcross⟩ :=
      Poincare.LinearAlgebra.exists_orthonormal_crossProduct_of_norm_eq_one w hw
    have h := hplane (∑ i, u i • b i) (∑ i, v i • b i)
    rw [multilinear_plane_expansion T b u v] at h
    change 0 ≤ ∑ i, ∑ j, (∑ k, ∑ l, R i j k l * u k * v l) * u i * v j at h
    rw [curvature_contraction_eq_crossProduct_rayleigh R hRf hRl, hcross] at h
    simpa only [curvatureOperator_rayleigh] using h
  have hnonneg (w : EuclideanSpace ℝ (Fin 3)) :
      0 ≤ inner ℝ w (curvatureOperator R w) := by
    by_cases hw : w = 0
    · simp [hw]
    have hinv : 0 < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
    have hnorm : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    have h := hunit (‖w‖⁻¹ • w) hnorm
    simp only [map_smul, real_inner_smul_left, inner_smul_right] at h
    exact nonneg_of_mul_nonneg_right (nonneg_of_mul_nonneg_right h hinv) hinv
  rw [skew_curvature_contraction R hRf hRl A hA]
  exact mul_nonneg (by norm_num) (hnonneg _)

end PoincareConjecture.M35

namespace PoincareConjecture.LeviCivitaData



theorem nonnegativeCurvatureOperator_of_nonnegative_sectional_three
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hsec : ∀ u v : TangentSpace (𝓡 3) x, 0 ≤ D.curvatureTensor x u v u v) :
    D.NonnegativeCurvatureOperator x := by
  classical
  obtain ⟨T, hT⟩ := hD.1.1 x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
  let e := (finCongr hdim).symm
  let b := fun i : Fin 3 => g.orthonormalBasis x (e i)
  have ht (u v w z : TangentSpace (𝓡 3) x) : T ![u, v, w, z] =
      D.curvatureTensor x u v w z := (hT _).symm
  have hlast (u v w z : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x u v w z = -D.curvatureTensor x u v z w :=
    (hD.2.2.2.1 x u v w z).1
  have hpair (u v w z : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x u v w z = D.curvatureTensor x w z u v :=
    (hD.2.2.2.1 x u v w z).2.1
  have hfirst (u v w z : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x u v w z = -D.curvatureTensor x v u w z := by
    rw [hpair u v w z, hlast w z u v, hpair w z v u]
  intro A hA
  have h := M35.three_frame_operator_nonneg T b
    (fun u v w z => by simpa only [ht] using hfirst u v w z)
    (fun u v w z => by simpa only [ht] using hlast u v w z)
    (fun u v => by simpa only [ht] using hsec u v)
    (fun i j => A (e i) (e j)) (fun i j => hA (e i) (e j))
  change 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l,
    A i j * A k l * D.curvatureTensor x (g.orthonormalBasis x i)
      (g.orthonormalBasis x j) (g.orthonormalBasis x k) (g.orthonormalBasis x l)
  simp only [← e.sum_comp]
  simpa only [ht] using h



theorem curvatureOperatorBound_of_curvatureTensorNorm_le
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) {K : ℝ}
    (hK : D.curvatureTensorNorm x ≤ K) : D.CurvatureOperatorBound K x := by
  intro A _
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let R := fun i j k l : I => D.curvatureTensor x (g.orthonormalBasis x i)
    (g.orthonormalBasis x j) (g.orthonormalBasis x k) (g.orthonormalBasis x l)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z : (I × I) × (I × I) => A z.1.1 z.1.2 * A z.2.1 z.2.2)
    (fun z : (I × I) × (I × I) => R z.1.1 z.1.2 z.2.1 z.2.2)
  have hsquare : (∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l) ^ 2 ≤
      (∑ i, ∑ j, A i j ^ 2) ^ 2 * (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) := by
    simpa only [Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum,
      ← Finset.sum_mul, ← pow_two] using hCS
  have hA : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hR : 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
  apply le_trans (b := D.curvatureTensorNorm x * ∑ i, ∑ j, A i j ^ 2)
  · change |∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l| ≤
      Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) * ∑ i, ∑ j, A i j ^ 2
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt hR]
    nlinarith [hsquare]
  · exact mul_le_mul_of_nonneg_right hK hA

end PoincareConjecture.LeviCivitaData
