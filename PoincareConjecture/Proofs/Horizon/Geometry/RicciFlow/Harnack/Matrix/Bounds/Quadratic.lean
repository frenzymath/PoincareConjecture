import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Perturbation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle BigOperators

namespace Poincare.RicciFlow.Harnack

private lemma sum_abs_le_card_mul_sqrt_sum_sq
    {I : Type*} [Fintype I] (W : I → ℝ) :
    (∑ i, |W i|) ≤ Fintype.card I * Real.sqrt (∑ i, (W i) ^ 2) := by
  classical
  calc
    _ ≤ ∑ _i : I, Real.sqrt (∑ i, (W i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [sq_abs, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (W j)) (Finset.mem_univ i)
    _ = _ := by simp

private lemma sum_abs_mul_le_of_bound
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℝ) (U : I → ℝ) (W : J → ℝ) (C : ℝ)
    (hA : ∀ i j, |A i j| ≤ C) :
    |∑ i, ∑ j, A i j * U i * W j| ≤ C * (∑ i, |U i|) * ∑ j, |W j| := by
  calc
    _ ≤ ∑ i, |∑ j, A i j * U i * W j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * U i * W j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, C * |U i| * |W j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

universe u

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hamilton_quadratic_lower_bound
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {τ : ℝ} (hτ : 0 ≤ τ) (x : M) (hcurv : D.NonnegativeCurvatureOperator x)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ i j, U i j = -U j i) :
    let b := g.orthonormalBasis x
    let C := 2 * (n : ℝ) ^ 4 * D.curvatureDerivativeNorm 2 x +
      3 * (n : ℝ) ^ 5 * (D.curvatureDerivativeNorm 0 x) ^ 2 +
      4 * (n : ℝ) ^ 4 * D.curvatureDerivativeNorm 1 x;
    -C * (Real.sqrt (∑ i, (W i) ^ 2)) ^ 2 -
      C * Real.sqrt (∑ i, ∑ j, (U i j) ^ 2) * Real.sqrt (∑ i, (W i) ^ 2) ≤
        (∑ i, ∑ j, hamiltonM D τ x (b i) (b j) * W i * W j) +
        2 * (∑ i, ∑ j, ∑ k, hamiltonP D x (b i) (b j) (b k) * U i j * W k) +
        (∑ i, ∑ j, ∑ k, ∑ l, D.curvatureTensor x (b i) (b j) (b k) (b l) *
          U i j * U k l) := by
  classical
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let CM := 2 * (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x +
    3 * (n : ℝ) ^ 3 * (D.curvatureDerivativeNorm 0 x) ^ 2
  let CP := 2 * (n : ℝ) * D.curvatureDerivativeNorm 1 x
  let B : I → I → ℝ := fun i j => hamiltonM D τ x (b i) (b j) -
    D.ricci x (b i) (b j) / (2 * τ)
  let u := Real.sqrt (∑ i, ∑ j, (U i j) ^ 2)
  let w := Real.sqrt (∑ i, (W i) ^ 2)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have h₁ : 0 ≤ D.curvatureDerivativeNorm 1 x := Real.sqrt_nonneg _
  have h₂ : 0 ≤ D.curvatureDerivativeNorm 2 x := Real.sqrt_nonneg _
  have hCM : 0 ≤ CM := by dsimp [CM]; positivity
  have hCP : 0 ≤ CP := by dsimp [CP]; positivity
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  have hb (i : I) : g.tangentNorm x (b i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Real.sqrt (inner ℝ (b i) (b i)) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  have hB (i j : I) : |B i j| ≤ CM := by
    simpa only [B, CM, hb, mul_one] using
      abs_hamiltonM_sub_ricci_le_curvatureDerivativeNorm D hD τ x (b i) (b j)
  have hP (i j k : I) : |hamiltonP D x (b i) (b j) (b k)| ≤ CP := by
    simpa only [CP, hb, mul_one] using
      abs_hamiltonP_le_curvatureDerivativeNorm D hD x (b i) (b j) (b k)
  have hW : (∑ i, |W i|) ≤ (n : ℝ) * w := by
    simpa only [Fintype.card_fin, hdim, w] using sum_abs_le_card_mul_sqrt_sum_sq W
  have hUs : (∑ i, ∑ j, |U i j|) ≤ (n : ℝ) ^ 2 * u := by
    simpa only [Fintype.sum_prod_type, Fintype.card_prod, I, Fintype.card_fin,
      hdim, Nat.cast_mul, ← pow_two, Nat.cast_pow, u] using
      sum_abs_le_card_mul_sqrt_sum_sq (fun ij : I × I => U ij.1 ij.2)
  have hBsum : |∑ i, ∑ j, B i j * W i * W j| ≤ CM * (n : ℝ) ^ 2 * w ^ 2 := by
    have h := sum_abs_mul_le_of_bound B W W CM hB
    have hprod := mul_le_mul hW hW (Finset.sum_nonneg (fun i _ => abs_nonneg _))
      (by positivity)
    have hc := mul_le_mul_of_nonneg_left hprod hCM
    nlinarith only [h, hc]
  have hPsum : |∑ i, ∑ j, ∑ k, hamiltonP D x (b i) (b j) (b k) * U i j * W k| ≤
      CP * (n : ℝ) ^ 3 * u * w := by
    have h := sum_abs_mul_le_of_bound
      (fun ij : I × I => fun k => hamiltonP D x (b ij.1) (b ij.2) (b k))
      (fun ij => U ij.1 ij.2) W CP (fun ij k => hP ij.1 ij.2 k)
    simp only [Fintype.sum_prod_type] at h
    have hprod := mul_le_mul hUs hW (Finset.sum_nonneg (fun i _ => abs_nonneg _))
      (by positivity)
    have hc := mul_le_mul_of_nonneg_left hprod hCP
    nlinarith only [h, hc]
  let R : I → I → I → I → ℝ := fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hlast : ∀ i j k l, R i j k l = -R i j l k :=
    fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).1
  have hpair : ∀ i j k l, R i j k l = R k l i j :=
    fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1
  have hfirst : ∀ i j k l, R i j k l = -R j i k l := by
    intro i j k l
    rw [hpair, hlast, hpair k l j i]
  have hop : ∀ A : I → I → ℝ, (∀ i j, A i j = -A j i) →
      0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * A i j * A k l := by
    intro A hA
    simpa only [LeviCivitaData.curvatureOperatorQuadratic, R, b,
      mul_comm, mul_left_comm, mul_assoc] using hcurv A hA
  have hRic := Poincare.Geometry.Curvature.Operator.curvature_operator_ricci_trace R
    (fun i j => D.ricci x (b i) (b j)) hfirst hlast (fun _ _ => rfl) W hop
  have hRicTime : 0 ≤ (∑ i, ∑ j, D.ricci x (b i) (b j) * W i * W j) / (2 * τ) :=
    div_nonneg hRic (by positivity)
  have hMsplit : (∑ i, ∑ j, hamiltonM D τ x (b i) (b j) * W i * W j) =
      (∑ i, ∑ j, B i j * W i * W j) +
        (∑ i, ∑ j, D.ricci x (b i) (b j) * W i * W j) / (2 * τ) := by
    simp only [B, sub_mul, Finset.sum_sub_distrib, Finset.sum_div,
      div_mul_eq_mul_div]
    ring
  have hR := hop U hU
  have hBlower := (abs_le.mp hBsum).1
  have hPlower := (abs_le.mp hPsum).1
  have hMextra : 0 ≤ CM * (n : ℝ) ^ 2 * u * w := by positivity
  have hPextra : 0 ≤ 2 * CP * (n : ℝ) ^ 3 * w ^ 2 := by positivity
  dsimp only
  change _ ≤ (∑ i, ∑ j, hamiltonM D τ x (b i) (b j) * W i * W j) + _ + _
  rw [hMsplit]
  dsimp only [CM, CP, u, w, R] at hBlower hPlower hMextra hPextra hR
  nlinarith only [hBlower, hPlower, hMextra, hPextra, hRicTime, hR]

theorem hamilton_quadratic_lower_bound_of_bound
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {τ : ℝ} (hτ : 0 ≤ τ) (x : M) (hcurv : D.NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : ∀ j ≤ 2, D.curvatureDerivativeNorm j x ≤ K)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ i j, U i j = -U j i) :
    let b := g.orthonormalBasis x
    let C := 6 * (n : ℝ) ^ 4 * K + 3 * (n : ℝ) ^ 5 * K ^ 2;
    -C * (Real.sqrt (∑ i, (W i) ^ 2)) ^ 2 -
      C * Real.sqrt (∑ i, ∑ j, (U i j) ^ 2) * Real.sqrt (∑ i, (W i) ^ 2) ≤
        (∑ i, ∑ j, hamiltonM D τ x (b i) (b j) * W i * W j) +
        2 * (∑ i, ∑ j, ∑ k, hamiltonP D x (b i) (b j) (b k) * U i j * W k) +
        (∑ i, ∑ j, ∑ k, ∑ l, D.curvatureTensor x (b i) (b j) (b k) (b l) *
          U i j * U k l) := by
  have hK₀ := hK 0 (by decide)
  have hK₁ := hK 1 (by decide)
  have hK₂ := hK 2 (by decide)
  have hnonneg : 0 ≤ D.curvatureDerivativeNorm 0 x := Real.sqrt_nonneg _
  have hKnonneg : 0 ≤ K := hnonneg.trans hK₀
  have hC : 2 * (n : ℝ) ^ 4 * D.curvatureDerivativeNorm 2 x +
      3 * (n : ℝ) ^ 5 * (D.curvatureDerivativeNorm 0 x) ^ 2 +
      4 * (n : ℝ) ^ 4 * D.curvatureDerivativeNorm 1 x ≤
        6 * (n : ℝ) ^ 4 * K + 3 * (n : ℝ) ^ 5 * K ^ 2 := by
    calc
      _ ≤ 2 * (n : ℝ) ^ 4 * K + 3 * (n : ℝ) ^ 5 * K ^ 2 +
          4 * (n : ℝ) ^ 4 * K := by gcongr
      _ = _ := by ring
  have h := hamilton_quadratic_lower_bound D hD hτ x hcurv U W hU
  dsimp only at h ⊢
  apply le_trans _ h
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_right (neg_le_neg hC) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Poincare.RicciFlow.Harnack
