import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.Divergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Reaction.DerivativeP
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Reaction.Contractions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

lemma tensorHeatOperator_divergence_hamiltonP_collected
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (a b : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
      hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
    F.tensorHeatOperator (fun s => (F.metric s).tensorTrace
        ((F.connection s).covariantTensorDerivative (P s))) t x ![a, b] =
      2 * (∑ k, ∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative (P t) x ![e k, e k, e i, e j]) +
      2 * (∑ i, ∑ j, D.ricci x (e i) (e j) *
        D.covariantTensorDerivative (P t) x ![e i, e j, a, b]) +
      (∑ i, ∑ j, hamiltonP D x (e i) (e j) a * hamiltonP D x (e i) (e j) b) -
      2 * (∑ i, ∑ j, hamiltonP D x a (e i) (e j) * hamiltonP D x b (e j) (e i)) +
      2 * (∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x ![e k, a, e i, b, e j] *
        D.covariantTensorDerivative D.ricciEvaluation x ![e k, e i, e j]) -
      2 * (∑ k, ∑ i, ∑ j, D.ricci x (e i) (e j) * D.covariantTensorDerivative
        (D.covariantTensorDerivative D.riemannEvaluation) x ![e k, e i, e k, a, b, e j]) := by
  let D := F.connection t
  let e := (F.metric t).orthonormalBasis x
  let P : CovariantTensorEvaluation n M 3 := fun y z => hamiltonP D y (z 0) (z 1) (z 2)
  have hD := hC.tensor_calculus n M (F.metric t) D
  have h := tensorHeatOperator_divergence_hamiltonP hC F ht x a b
  dsimp only at h ⊢
  have hder (k) := covariantTensorDerivative_hamiltonPReaction D hD x (e k) (e k) a b
  have htrace : (F.metric t).tensorTrace (D.covariantTensorDerivative (hamiltonPReaction D)) x ![a, b] =
      ∑ k, D.covariantTensorDerivative (hamiltonPReaction D) x ![e k, e k, a, b] := rfl
  rw [htrace] at h
  simp_rw [hder] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have ha := curvature_skew_contraction D hD x a
    (fun p q r => D.covariantTensorDerivative P x ![p, q, r, b])
  have hb := curvature_skew_contraction D hD x b
    (fun p q r => D.covariantTensorDerivative P x ![p, q, a, r])
  have hdiva := curvature_divergence_contraction D hD x a (fun p q => hamiltonP D x p q b)
  have hdivb := curvature_divergence_contraction D hD x b (fun p q => hamiltonP D x p a q)
  have hquad := hamiltonP_quadratic_contraction D hD x a b
  have hgrad := hamiltonP_curvature_gradient_contraction D hD x a b
  dsimp only [D, e, P] at ha hb hdiva hdivb hquad hgrad h
  linarith only [h, ha, hb, hdiva, hdivb, hquad, hgrad]

lemma tensorHeatOperator_divergence_hamiltonP_reaction
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (a b : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
      hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
    F.tensorHeatOperator (fun s => (F.metric s).tensorTrace
        ((F.connection s).covariantTensorDerivative (P s))) t x ![a, b] =
      2 * (∑ k, ∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative (P t) x ![e k, e k, e i, e j]) +
      2 * (∑ i, ∑ j, D.ricci x (e i) (e j) *
        (D.covariantTensorDerivative (P t) x ![e i, e j, a, b] +
          D.covariantTensorDerivative (P t) x ![e i, e j, b, a])) +
      (∑ i, ∑ j, hamiltonP D x (e i) (e j) a * hamiltonP D x (e i) (e j) b) -
      2 * (∑ i, ∑ j, hamiltonP D x a (e i) (e j) * hamiltonP D x b (e j) (e i)) +
      2 * (∑ i, ∑ j, ∑ k, D.ricci x (e i) (e j) * D.ricci x (e i) (e k) *
        D.curvatureTensor x a (e k) b (e j)) +
      2 * (∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x ![e k, a, e i, b, e j] *
        D.covariantTensorDerivative D.ricciEvaluation x ![e k, e i, e j]) -
      2 * (∑ i, ∑ j, D.ricci x (e i) (e j) *
        (D.curvatureB x (e i) a (e j) b - D.curvatureB x (e i) a b (e j) +
          D.curvatureB x (e i) (e j) a b - D.curvatureB x (e i) b a (e j))) := by
  have hD := hC.tensor_calculus n M (F.metric t) (F.connection t)
  have h := tensorHeatOperator_divergence_hamiltonP_collected hC F ht x a b
  dsimp only at h ⊢
  rw [ricci_second_curvature_contraction (F.connection t) hD] at h
  simp only [mul_add, Finset.sum_add_distrib]
  linarith only [h]

end Poincare.RicciFlow.Harnack
