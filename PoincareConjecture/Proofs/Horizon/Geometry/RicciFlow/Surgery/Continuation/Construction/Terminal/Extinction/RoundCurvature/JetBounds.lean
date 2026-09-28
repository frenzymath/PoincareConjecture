import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.NormBounds







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.SingularRoundComponent

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)

def metricError : CovariantTensorEvaluation 3 N.model.carrier 2 :=
  fun x v => N.scale * singularMetricPullback g N.forward x v -
    N.model_metric.inner x (v 0) (v 1)

theorem covariantJet_norm_lt (j : ℕ) (hj : j ≤ ⌊epsilon⁻¹⌋₊)
    (x : N.model.carrier) :
    N.model_metric.tensorNorm
      (N.model_connection.iteratedCovariantTensorDerivative N.metricError j) x < epsilon := by
  obtain ⟨bound, hbound, hjet⟩ := N.metric_comparison
  have hterm := Finset.single_le_sum (s := Finset.range (⌊epsilon⁻¹⌋₊ + 1)) (a := j)
    (f := fun k => (N.model_metric.tensorNorm
      (N.model_connection.iteratedCovariantTensorDerivative N.metricError k) x) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hsquare : (N.model_metric.tensorNorm
      (N.model_connection.iteratedCovariantTensorDerivative N.metricError j) x) ^ 2 <
        epsilon ^ 2 := hterm.trans_lt ((hjet x).trans_lt hbound)
  nlinarith [N.epsilon_pos]

include N in
theorem two_le_comparison_order (hepsilon : epsilon ≤ 1 / 200) :
    2 ≤ ⌊epsilon⁻¹⌋₊ := by
  apply Nat.le_floor
  have hi := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 200) N.epsilon_pos).mpr hepsilon
  norm_num at hi ⊢
  linarith

theorem covariantTwoJet_norm_lt (hepsilon : epsilon ≤ 1 / 200)
    (j : ℕ) (hj : j ≤ 2) (x : N.model.carrier) :
    N.model_metric.tensorNorm
      (N.model_connection.iteratedCovariantTensorDerivative N.metricError j) x < epsilon :=
  N.covariantJet_norm_lt j (hj.trans (N.two_le_comparison_order hepsilon)) x


theorem covariantJet_component_lt (j : ℕ) (hj : j ≤ ⌊epsilon⁻¹⌋₊)
    (x : N.model.carrier)
    (a : Fin (2 + j) → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
    |N.model_connection.iteratedCovariantTensorDerivative N.metricError j x
      (fun i => N.model_metric.orthonormalBasis x (a i))| < epsilon := by
  have hnorm := N.covariantJet_norm_lt j hj x
  let T := N.model_connection.iteratedCovariantTensorDerivative N.metricError j
  have hterm := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b : Fin (2 + j) → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)) =>
      (T x (fun i => N.model_metric.orthonormalBasis x (b i))) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  have hsqrt : (N.model_metric.tensorNorm T x) ^ 2 =
      ∑ b : Fin (2 + j) → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        (T x (fun i => N.model_metric.orthonormalBasis x (b i))) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hnonneg : 0 ≤ N.model_metric.tensorNorm T x := Real.sqrt_nonneg _
  change |T x (fun i => N.model_metric.orthonormalBasis x (a i))| < epsilon
  rw [abs_lt]
  constructor <;> nlinarith

theorem bilinear_error_le (x : N.model.carrier) (v w : TangentSpace (𝓡 3) x) :
    |N.scale * g.inner (N.forward x)
        (mfderiv (𝓡 3) (𝓡 3) N.forward x v)
        (mfderiv (𝓡 3) (𝓡 3) N.forward x w) - N.model_metric.inner x v w| ≤
      epsilon * N.model_metric.tangentNorm x v * N.model_metric.tangentNorm x w := by
  let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 3) x) ℝ :=
    { toFun := N.metricError x
      map_update_add' := by
        intro _ z i a b
        fin_cases i <;> simp [metricError, singularMetricPullback, map_add, mul_add] <;> ring
      map_update_smul' := by
        intro _ z i r a
        fin_cases i <;> simp [metricError, singularMetricPullback, map_smul, smul_eq_mul] <;> ring }
  have hnorm := N.covariantJet_norm_lt 0 (Nat.zero_le _) x
  have heval := abs_tensor_evaluation_le_tensorNorm N.model_metric N.metricError x A
    (fun _ => rfl) ![v, w]
  have hv : 0 ≤ N.model_metric.tangentNorm x v := Real.sqrt_nonneg _
  have hw : 0 ≤ N.model_metric.tangentNorm x w := Real.sqrt_nonneg _
  calc
    _ ≤ N.model_metric.tensorNorm N.metricError x *
        (N.model_metric.tangentNorm x v * N.model_metric.tangentNorm x w) := by
      simpa only [metricError, singularMetricPullback, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using heval
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hnorm.le (mul_nonneg hv hw)
      simpa only [LeviCivitaData.iteratedCovariantTensorDerivative, mul_assoc] using h

theorem quadratic_bounds (x : N.model.carrier) (v : TangentSpace (𝓡 3) x) :
    (1 - epsilon) * N.model_metric.inner x v v ≤
      N.scale * g.inner (N.forward x)
        (mfderiv (𝓡 3) (𝓡 3) N.forward x v)
        (mfderiv (𝓡 3) (𝓡 3) N.forward x v) ∧
      N.scale * g.inner (N.forward x)
        (mfderiv (𝓡 3) (𝓡 3) N.forward x v)
        (mfderiv (𝓡 3) (𝓡 3) N.forward x v) ≤
          (1 + epsilon) * N.model_metric.inner x v v := by
  have hnonneg : 0 ≤ N.model_metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (N.model_metric.pos x v hv).le
  have he := N.bilinear_error_le x v v
  have hn : N.model_metric.tangentNorm x v * N.model_metric.tangentNorm x v =
      N.model_metric.inner x v v := (pow_two _).symm.trans (Real.sq_sqrt hnonneg)
  rw [mul_assoc, hn] at he
  obtain ⟨hlower, hupper⟩ := abs_le.mp he
  constructor <;> nlinarith

end PoincareConjecture.SingularRoundComponent
