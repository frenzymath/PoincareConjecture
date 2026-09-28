import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ContractedBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.GradientTime

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47Positive

private noncomputable def bianchiProjection {ι : Type*} [DecidableEq ι]
    (X : ι → ℝ) (i j k : ι) : ℝ :=
  (if j = k then (3 / 10 : ℝ) * X i else 0) +
    (if i = k then (1 / 20 : ℝ) * X j else 0) +
    (if i = j then (1 / 20 : ℝ) * X k else 0)

private theorem bianchi_projection_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ι → ι → ℝ) (X : ι → ℝ)
    (hsym : ∀ i j k, T i j k = T i k j)
    (htrace : ∀ i, ∑ j, T i j j = X i)
    (hdiv : ∀ i, ∑ j, T j i j = X i / 2) :
    (∑ i, ∑ j, ∑ k, T i j k * bianchiProjection X i j k) =
      (7 / 20 : ℝ) * ∑ i, (X i) ^ 2 := by
  have h1 : (∑ i, ∑ j, T i j j * ((3 / 10 : ℝ) * X i)) =
      (3 / 10 : ℝ) * ∑ i, (X i) ^ 2 := by
    simp only [← Finset.sum_mul, htrace]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i, ∑ j, T i j i * ((1 / 20 : ℝ) * X j)) =
      (1 / 40 : ℝ) * ∑ i, (X i) ^ 2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hdiv]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h3 : (∑ i, ∑ k, T i i k * ((1 / 20 : ℝ) * X k)) =
      (1 / 40 : ℝ) * ∑ i, (X i) ^ 2 := by
    calc
      _ = ∑ i, ∑ k, T i k i * ((1 / 20 : ℝ) * X k) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        rw [hsym i i k]
      _ = _ := h2
  simp only [bianchiProjection, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [h1, h2, h3]
  ring

theorem ricci_derivative_trace_improved {ι : Type*} [Fintype ι]
    (hdim : Fintype.card ι = 3) (T : ι → ι → ι → ℝ) (X : ι → ℝ)
    (hsym : ∀ i j k, T i j k = T i k j)
    (htrace : ∀ i, ∑ j, T i j j = X i)
    (hdiv : ∀ i, ∑ j, T j i j = X i / 2) :
    (7 / 20 : ℝ) * (∑ i, (X i) ^ 2) ≤ ∑ i, ∑ j, ∑ k, (T i j k) ^ 2 := by
  classical
  let B := bianchiProjection X
  have hBsym (i j k : ι) : B i j k = B i k j := by
    simp only [B, bianchiProjection, eq_comm]
    ring
  have hBtrace (i : ι) : ∑ j, B i j j = X i := by
    simp [B, bianchiProjection, Finset.sum_add_distrib, hdim]
    ring
  have hBdiv (i : ι) : ∑ j, B j i j = X i / 2 := by
    simp [B, bianchiProjection, Finset.sum_add_distrib, hdim]
    ring
  have hpair := bianchi_projection_pairing T X hsym htrace hdiv
  have hnorm := bianchi_projection_pairing B X hBsym hBtrace hBdiv
  change (∑ i, ∑ j, ∑ k, T i j k * B i j k) = _ at hpair
  change (∑ i, ∑ j, ∑ k, B i j k * B i j k) = _ at hnorm
  have hnonneg : 0 ≤ ∑ i, ∑ j, ∑ k, (T i j k - B i j k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hid : (∑ i, ∑ j, ∑ k, (T i j k - B i j k) ^ 2) =
      (∑ i, ∑ j, ∑ k, (T i j k) ^ 2) -
        2 * (∑ i, ∑ j, ∑ k, T i j k * B i j k) +
          (∑ i, ∑ j, ∑ k, B i j k * B i j k) := by
    calc
      _ = ∑ i, ∑ j, ∑ k,
          ((T i j k) ^ 2 - 2 * (T i j k * B i j k) + B i j k * B i j k) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hid, hpair, hnorm] at hnonneg
  linarith only [hnonneg]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem scalar_gradient_le_ricci_derivative (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    (7 / 20 : ℝ) * g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) ≤
      ∑ k, ∑ i, ∑ j, (D.covariantTensorDerivative D.ricciEvaluation x
        ![g.orthonormalBasis x k, g.orthonormalBasis x i, g.orthonormalBasis x j]) ^ 2 := by
  have hdim : Fintype.card (Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) = 3 := by
    rw [Fintype.card_fin, VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)),
      finrank_euclideanSpace]
    simp
  have hsym (i j k : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      D.frameRicciDerivative x i j k = D.frameRicciDerivative x i k j :=
    D.covariantTensorDerivative_ricciEvaluation_symm hD x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j) (g.orthonormalBasis x k)
  have h := ricci_derivative_trace_improved hdim (D.frameRicciDerivative x)
    (D.frameScalarDerivative x) hsym
    (D.frameRicciDerivative_scalar_trace hD x) (D.frameRicciDerivative_trace hD x)
  rw [D.gradient_normSq_eq_sum_mvfderiv_sq]
  exact h

end PoincareConjecture.M47Positive
