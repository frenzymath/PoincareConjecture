import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Linearity










set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem weighted_square {theta : ℝ} (htheta : 0 < theta) (a b : ℝ) :
    a ^ 2 ≤ (1 + theta) * b ^ 2 + (1 + theta⁻¹) * (a - b) ^ 2 := by
  have hid : theta * ((1 + theta) * b ^ 2 + (1 + theta⁻¹) * (a - b) ^ 2 - a ^ 2) =
      (theta * b - (a - b)) ^ 2 := by
    field_simp
    ring
  have h := sq_nonneg (theta * b - (a - b))
  rw [← hid] at h
  have hnonnegative := nonneg_of_mul_nonneg_right h htheta
  linarith



theorem limitCanonical_tensorNorm_weighted
    (g : RiemannianMetric n M) {r : ℕ}
    (T S : CovariantTensorEvaluation n M r) (x : M)
    {theta : ℝ} (htheta : 0 < theta) :
    g.tensorNorm T x ^ 2 ≤ (1 + theta) * g.tensorNorm S x ^ 2 +
      (1 + theta⁻¹) * g.tensorNorm (fun y v => T y v - S y v) x ^ 2 := by
  unfold RiemannianMetric.tensorNorm
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => weighted_square htheta _ _



theorem limitCanonical_iterated_covariant_sub {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {r : ℕ} {T S : CovariantTensorEvaluation n M r}
    (hT : IsSmoothCovariantTensor T) (hS : IsSmoothCovariantTensor S) (m : ℕ) :
    D.iteratedCovariantTensorDerivative (fun y v => T y v - S y v) m =
      fun y v => D.iteratedCovariantTensorDerivative T m y v -
        D.iteratedCovariantTensorDerivative S m y v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change D.covariantTensorDerivative
        (D.iteratedCovariantTensorDerivative (fun y v => T y v - S y v) m) =
      fun y v => D.covariantTensorDerivative (D.iteratedCovariantTensorDerivative T m) y v -
        D.covariantTensorDerivative (D.iteratedCovariantTensorDerivative S m) y v
    rw [ih]
    exact D.covariantTensorDerivative_sub
      (D.iteratedCovariantTensorDerivative_isSmooth hT m)
      (D.iteratedCovariantTensorDerivative_isSmooth hS m)



theorem limitCanonical_tensorJetEnergy_weighted {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {r : ℕ} {T S : CovariantTensorEvaluation n M r}
    (hT : IsSmoothCovariantTensor T) (hS : IsSmoothCovariantTensor S)
    (m : ℕ) (x : M) {theta : ℝ} (htheta : 0 < theta) :
    (∑ j ∈ Finset.range (m + 1),
      g.tensorNorm (D.iteratedCovariantTensorDerivative T j) x ^ 2) ≤
      (1 + theta) * (∑ j ∈ Finset.range (m + 1),
        g.tensorNorm (D.iteratedCovariantTensorDerivative S j) x ^ 2) +
      (1 + theta⁻¹) * (∑ j ∈ Finset.range (m + 1),
        g.tensorNorm (D.iteratedCovariantTensorDerivative (fun y v => T y v - S y v) j) x ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  rw [limitCanonical_iterated_covariant_sub D hT hS]
  exact limitCanonical_tensorNorm_weighted g _ _ x htheta

section Comparison

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]



theorem limitCanonical_comparisonEnergy_weighted
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    {B C : CovariantTensorEvaluation 3 X 2}
    (hB : IsSmoothCovariantTensor B) (hC : IsSmoothCovariantTensor C)
    (m : ℕ) (x : X) {theta : ℝ} (htheta : 0 < theta) :
    singularMetricJetErrorSquared g D B m x ≤
      (1 + theta) * singularMetricJetErrorSquared g D C m x +
      (1 + theta⁻¹) * (∑ j ∈ Finset.range (m + 1),
        g.tensorNorm (D.iteratedCovariantTensorDerivative (fun y v => B y v - C y v) j) x ^ 2) := by
  have h := limitCanonical_tensorJetEnergy_weighted D
    (hB.sub (M44.isSmoothCovariantTensor_metric g))
    (hC.sub (M44.isSmoothCovariantTensor_metric g)) m x htheta
  have heq : (fun y v => (B y v - g.inner y (v 0) (v 1)) -
      (C y v - g.inner y (v 0) (v 1))) = (fun y v => B y v - C y v) := by
    funext y v
    ring
  rw [heq] at h
  exact h




theorem limitCanonical_exists_strict_comparison_margin
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (C : CovariantTensorEvaluation 3 X 2) (hC : IsSmoothCovariantTensor C)
    (m : ℕ) (U : Set X) {epsilon b : ℝ} (hb : b < epsilon ^ 2)
    (hbound : ∀ x ∈ U, singularMetricJetErrorSquared g D C m x ≤ b) :
    ∃ eta b' : ℝ, 0 < eta ∧ b' < epsilon ^ 2 ∧
      ∀ B : CovariantTensorEvaluation 3 X 2, IsSmoothCovariantTensor B →
        (∀ x ∈ U, (∑ j ∈ Finset.range (m + 1),
          g.tensorNorm (D.iteratedCovariantTensorDerivative
            (fun y v => B y v - C y v) j) x ^ 2) ≤ eta) →
        ∀ x ∈ U, singularMetricJetErrorSquared g D B m x ≤ b' := by
  let theta := (epsilon ^ 2 - b) / (2 * (|b| + 1))
  have htheta : 0 < theta := div_pos (sub_pos.mpr hb) (by positivity)
  have hthetab : theta * (|b| + 1) = (epsilon ^ 2 - b) / 2 := by
    dsimp only [theta]
    field_simp
  have hscaled : theta * b ≤ (epsilon ^ 2 - b) / 2 := by
    calc
      _ ≤ theta * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) htheta.le
      _ ≤ theta * (|b| + 1) := mul_le_mul_of_nonneg_left (by linarith) htheta.le
      _ = _ := hthetab
  have hbase : (1 + theta) * b < epsilon ^ 2 := by nlinarith
  let gap := epsilon ^ 2 - (1 + theta) * b
  have hgap : 0 < gap := sub_pos.mpr hbase
  let eta := gap / (2 * (1 + theta⁻¹))
  have hcoef : 0 < 1 + theta⁻¹ := by positivity
  have heta : 0 < eta := div_pos hgap (by positivity)
  have heq : (1 + theta⁻¹) * eta = gap / 2 := by
    dsimp only [eta]
    field_simp
  refine ⟨eta, (1 + theta) * b + (1 + theta⁻¹) * eta, heta, ?_, ?_⟩
  · rw [heq]
    dsimp only [gap]
    linarith only [hbase]
  · intro B hB herror x hx
    exact (limitCanonical_comparisonEnergy_weighted g D hB hC m x htheta).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left (hbound x hx) (by positivity))
        (mul_le_mul_of_nonneg_left (herror x hx) hcoef.le))

end Comparison

end PoincareConjecture.M47
