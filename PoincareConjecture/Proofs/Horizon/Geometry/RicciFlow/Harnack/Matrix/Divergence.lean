import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Derivatives
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ContractedBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.CurvatureAction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma sum_covariantTensorDerivative_ricci_divergence
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative D.ricciEvaluation x
      ![g.orthonormalBasis x i, v, g.orthonormalBasis x i]) =
      mvfderiv (𝓡 n) D.scalarCurvature x v / 2 := by
  rw [← D.sum_covariantTensorDerivative_ricci_eq_scalar_derivative hD x v]
  simp_rw [D.covariantTensorDerivative_ricciEvaluation_eq_sum_riemann hD]
  exact double_contraction_second_bianchi
    (fun a b c d e => D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e])
    (g.orthonormalBasis x)
    (D.covariantTensorDerivative_riemannEvaluation_skew_first hD x)
    (D.covariantTensorDerivative_riemannEvaluation_skew_last hD x)
    (D.covariantTensorDerivative_curvature_second_bianchi hD x) v

lemma sum_secondCovariantTensorDerivative_ricci_divergence
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative D.ricciEvaluation) x
      ![u, g.orthonormalBasis x i, g.orthonormalBasis x i, v]) =
      D.hessian D.scalarCurvature x u v / 2 := by
  let A := D.covariantTensorDerivative D.ricciEvaluation
  have hA := hD.2.2.1 2 D.ricciEvaluation hD.2.1
  have htrace : g.tensorTrace A =
      fun y z => mvfderiv (𝓡 n) D.scalarCurvature y (z 0) / 2 := by
    funext y z
    have hz : z = ![z 0] := by ext i; fin_cases i; rfl
    rw [hz]
    change (∑ i, A y ![g.orthonormalBasis y i, g.orthonormalBasis y i, z 0]) = _
    calc
      _ = ∑ i, D.covariantTensorDerivative D.ricciEvaluation y
          ![g.orthonormalBasis y i, z 0, g.orthonormalBasis y i] :=
        Finset.sum_congr rfl fun i _ =>
          D.covariantTensorDerivative_ricciEvaluation_symm hD y _ _ _
      _ = _ := D.sum_covariantTensorDerivative_ricci_divergence hD y (z 0)
  have h := D.covariantTensorDerivative_tensorTrace hA x u ![v]
  change D.covariantTensorDerivative (g.tensorTrace A) x ![u, v] = _ at h
  rw [htrace] at h
  simp only [Matrix.Fin.cons_vecCons] at h
  rw [← h]
  simp [covariantTensorDerivative, hessian, hessianOnFields,
    mvfderiv_const_mul, div_eq_mul_inv, mul_comm, mul_sub]

lemma sum_secondCovariantTensorDerivative_ricci_swap
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    (∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative D.ricciEvaluation) x
      ![b i, u, b i, v]) =
      D.hessian D.scalarCurvature x u v / 2 +
        (∑ i, D.ricci x u (b i) * D.ricci x (b i) v) -
        ∑ i, ∑ j, D.curvatureTensor x (b i) u (b j) v * D.ricci x (b i) (b j) := by
  let b := g.orthonormalBasis x
  have hfirst (a c d e : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a c d e = -D.curvatureTensor x c a d e := by
    rw [(hD.2.2.2.1 x a c d e).2.1, (hD.2.2.2.1 x d e a c).1,
      (hD.2.2.2.1 x d e c a).2.1]
  have hleft (i) : D.ricci x (D.curvature x (b i) u (b i)) v =
      ∑ j, D.curvatureTensor x (b i) u (b j) (b i) * D.ricci x (b j) v := by
    have h := D.tensor_curvature_slot_eq_sum hD.2.1 x ![b i, v] 0 (b i) u (b i)
    have hu (w : TangentSpace (𝓡 n) x) : Function.update ![b i, v] 0 w = ![w, v] := by
      ext k; fin_cases k <;> simp
    simpa only [hu, ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have hright (i) : D.ricci x (b i) (D.curvature x (b i) u v) =
      ∑ j, D.curvatureTensor x (b i) u (b j) v * D.ricci x (b i) (b j) := by
    have h := D.tensor_curvature_slot_eq_sum hD.2.1 x ![b i, v] 1 (b i) u v
    have hu (w : TangentSpace (𝓡 n) x) : Function.update ![b i, v] 1 w = ![b i, w] := by
      ext k; fin_cases k <;> simp
    simpa only [hu, ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have hleftsum : (∑ i, D.ricci x (D.curvature x (b i) u (b i)) v) =
      -(∑ j, D.ricci x u (b j) * D.ricci x (b j) v) := by
    simp_rw [hleft]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    have hc : (∑ i, D.curvatureTensor x (b i) u (b j) (b i)) = -D.ricci x u (b j) := by
      simp_rw [hfirst (b _) u]
      rw [Finset.sum_neg_distrib]
      rfl
    rw [hc, neg_mul]
  have hcomm := congrArg (fun f : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ =>
    ∑ i, f i) (funext fun i =>
      D.covariantTensorDerivative_commutator_two hD.2.1 x (b i) u (b i) v)
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hcomm
  rw [hleftsum] at hcomm
  simp_rw [hright] at hcomm
  have hdiv := D.sum_secondCovariantTensorDerivative_ricci_divergence hD x u v
  dsimp only at ⊢
  dsimp only [b] at hcomm
  linarith only [hcomm, hdiv]

end PoincareConjecture.LeviCivitaData

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hamiltonM_eq_divergence_hamiltonP
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (τ : ℝ) (x : M) (u v : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    hamiltonM D τ x u v =
      (∑ i, D.covariantTensorDerivative
        (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![b i, b i, u, v]) +
        (∑ i, ∑ j, D.curvatureTensor x (b i) u (b j) v * D.ricci x (b i) (b j)) +
        D.ricci x u v / (2 * τ) := by
  dsimp only
  simp_rw [covariantTensorDerivative_hamiltonP D hD]
  rw [Finset.sum_sub_distrib, D.sum_secondCovariantTensorDerivative_ricci_swap hD]
  simp only [hamiltonM, LeviCivitaData.tensorLaplacian,
    LeviCivitaData.iteratedCovariantTensorDerivative, Matrix.Fin.cons_vecCons]
  ring

end Poincare.RicciFlow.Harnack
