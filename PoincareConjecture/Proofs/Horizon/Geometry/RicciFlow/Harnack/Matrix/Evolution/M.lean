import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.DivergenceReaction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.TimeCorrection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatLinearity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Evolution.CurvatureRicci








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma differentiableAt_trace
    (F : RicciFlow n M J) {k : ℕ}
    {T : ℝ → CovariantTensorEvaluation n M (k + 2)}
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hd : ∀ z, DifferentiableAt ℝ (fun s => T s x z) t)
    (v : Fin k → TangentSpace (𝓡 n) x) :
    DifferentiableAt ℝ (fun s => (F.metric s).tensorTrace (T s) x v) t := by
  exact (F.hasDerivAt_tensorTrace
    (W := fun _ y z => deriv (fun s => T s y z) t) ht x hT
    (fun z => (hd z).hasDerivAt) v).differentiableAt

lemma differentiableAt_curvatureRicci
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (v : Fin 2 → TangentSpace (𝓡 n) x) :
    DifferentiableAt ℝ (fun s =>
      ∑ i, ∑ j, (F.connection s).curvatureTensor x (v 0)
        ((F.metric s).orthonormalBasis x i) (v 1) ((F.metric s).orthonormalBasis x j) *
        (F.connection s).ricci x ((F.metric s).orthonormalBasis x i)
          ((F.metric s).orthonormalBasis x j)) t := by
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![4, 0, 5, 2, 1, 3] (by decide)
  let S : ℝ → CovariantTensorEvaluation n M 6 := fun s y z =>
    tensorProduct (F.connection s).riemannEvaluation (F.connection s).ricciEvaluation
      y (z ∘ σ)
  have hS (s : ℝ) : IsSmoothCovariantTensor (S s) :=
    (isSmoothCovariantTensor_tensorProduct
      (hC.tensor_calculus n M (F.metric s) (F.connection s)).1
      (hC.tensor_calculus n M (F.metric s) (F.connection s)).2.1).perm σ
  have hd (z : Fin 6 → TangentSpace (𝓡 n) x) :
      DifferentiableAt ℝ (fun s => S s x z) t := by
    exact ((hC.curvature_evolution n M J F t (interior_subset ht) x
      (z (σ 0)) (z (σ 1)) (z (σ 2)) (z (σ 3))).hasDerivAt
        (mem_interior_iff_mem_nhds.mp ht)).differentiableAt.mul
      ((hC.ricci_evolution n M J F t (interior_subset ht) x
        (z (σ 4)) (z (σ 5))).hasDerivAt
          (mem_interior_iff_mem_nhds.mp ht)).differentiableAt
  have h := differentiableAt_trace F ht x
    (fun s => (hS s).tensorTrace (g := F.metric s))
    (fun z => differentiableAt_trace F ht x hS hd z) v
  simpa only [S, σ, ← LeviCivitaData.curvatureRicci_eq_double_trace] using h

lemma tensorHeatOperator_hamiltonM_decomposition
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
      hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
    let C : ℝ → CovariantTensorEvaluation n M 2 := fun s y z =>
      ∑ i, ∑ j, (F.connection s).curvatureTensor y (z 0)
        ((F.metric s).orthonormalBasis y i) (z 1) ((F.metric s).orthonormalBasis y j) *
        (F.connection s).ricci y ((F.metric s).orthonormalBasis y i)
          ((F.metric s).orthonormalBasis y j)
    F.tensorHeatOperator (fun s y z => hamiltonM (F.connection s) (s - T₀) y
        (z 0) (z 1)) t x ![a, b] =
      F.tensorHeatOperator (fun s => (F.metric s).tensorTrace
        ((F.connection s).covariantTensorDerivative (P s))) t x ![a, b] +
      F.tensorHeatOperator C t x ![a, b] +
      F.tensorHeatOperator (fun s y z =>
        (F.connection s).ricciEvaluation y z / (2 * (s - T₀))) t x ![a, b] := by
  let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
    hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
  let B : ℝ → CovariantTensorEvaluation n M 2 := fun s =>
    (F.metric s).tensorTrace ((F.connection s).covariantTensorDerivative (P s))
  let C : ℝ → CovariantTensorEvaluation n M 2 := fun s y z =>
    ∑ i, ∑ j, (F.connection s).curvatureTensor y (z 0)
      ((F.metric s).orthonormalBasis y i) (z 1) ((F.metric s).orthonormalBasis y j) *
      (F.connection s).ricci y ((F.metric s).orthonormalBasis y i)
        ((F.metric s).orthonormalBasis y j)
  let Q : ℝ → CovariantTensorEvaluation n M 2 := fun s y z =>
    (F.connection s).ricciEvaluation y z / (2 * (s - T₀))
  have hD (s) := hC.tensor_calculus n M (F.metric s) (F.connection s)
  have hB : IsSmoothCovariantTensor (B t) :=
    ((hD t).2.2.1 _ _ (hamiltonP_isSmoothCovariantTensor _ (hD t))).tensorTrace
  have hCs : IsSmoothCovariantTensor (C t) :=
    (F.connection t).isSmoothCovariantTensor_curvatureRicci (hD t)
  have hQ : IsSmoothCovariantTensor (Q t) := by
    simpa only [Q, div_eq_mul_inv, mul_comm] using
      (hD t).2.1.const_mul (2 * (t - T₀))⁻¹
  have hdB : DifferentiableAt ℝ (fun s => B s x ![a, b]) t :=
    (hasDerivAt_divergence_hamiltonP hC F ht x a b).differentiableAt
  have hdC : DifferentiableAt ℝ (fun s => C s x ![a, b]) t :=
    differentiableAt_curvatureRicci hC F ht x ![a, b]
  have hdQ : DifferentiableAt ℝ (fun s => Q s x ![a, b]) t :=
    ((hC.ricci_evolution n M J F t (interior_subset ht) x a b).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).differentiableAt.div
        (differentiableAt_const _ |>.mul (differentiableAt_id.sub_const T₀))
        (mul_ne_zero (by norm_num) hτ)
  have heq : (fun s y z => hamiltonM (F.connection s) (s - T₀) y (z 0) (z 1)) =
      (fun s y z => (B s y z + C s y z) + Q s y z) := by
    funext s y z
    have hz : z = ![z 0, z 1] := by ext i; fin_cases i <;> rfl
    rw [hz]
    rw [hamiltonM_eq_divergence_hamiltonP _ (hD s)]
    dsimp only [B, C, Q, P, RiemannianMetric.tensorTrace]
    apply congrArg (fun r : ℝ => _ + r + _)
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs := (hD s).2.2.2.1
    rw [(hs y _ _ _ _).2.1, (hs y _ _ _ _).1,
      (hs y _ _ _ _).2.1, (hs y _ _ _ _).1, neg_neg]
  rw [heq, F.tensorHeatOperator_add (hB.add hCs) hQ
    ((hD t).2.2.1 _ _ (hB.add hCs)) ((hD t).2.2.1 _ _ hQ)
    x ![a, b] (hdB.add hdC) hdQ,
    F.tensorHeatOperator_add hB hCs ((hD t).2.2.1 _ _ hB)
      ((hD t).2.2.1 _ _ hCs) x ![a, b] hdB hdC]



lemma curvature_contraction_hamiltonM
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (τ : ℝ)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    let P : CovariantTensorEvaluation n M 3 := fun y z =>
      hamiltonP D y (z 0) (z 1) (z 2)
    (∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
      hamiltonM D τ x (e i) (e j)) =
      (∑ k, ∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative P x ![e k, e k, e i, e j]) +
      (∑ i, ∑ j, ∑ k, ∑ l, D.curvatureTensor x a (e i) b (e j) *
        D.curvatureTensor x (e i) (e k) (e j) (e l) * D.ricci x (e k) (e l)) +
      (∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        (D.ricci x (e i) (e j) / (2 * τ))) := by
  dsimp only
  have hslot (i j k l) :
      D.curvatureTensor x (g.orthonormalBasis x k) (g.orthonormalBasis x i)
        (g.orthonormalBasis x l) (g.orthonormalBasis x j) =
      D.curvatureTensor x (g.orthonormalBasis x i) (g.orthonormalBasis x k)
        (g.orthonormalBasis x j) (g.orthonormalBasis x l) := by
    have hs := hD.2.2.2.1
    rw [(hs x _ _ _ _).2.1, (hs x _ _ _ _).1,
      (hs x _ _ _ _).2.1, (hs x _ _ _ _).1, neg_neg]
  simp_rw [hamiltonM_eq_divergence_hamiltonP D hD, hslot]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
  congr 2
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm




theorem tensorHeatOperator_hamiltonM
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    let P : CovariantTensorEvaluation n M 3 := fun y z =>
      hamiltonP D y (z 0) (z 1) (z 2)
    F.tensorHeatOperator (fun s y z => hamiltonM (F.connection s) (s - T₀) y
        (z 0) (z 1)) t x ![a, b] =
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        hamiltonM D (t - T₀) x (e i) (e j)) +
      2 * (∑ i, ∑ j, D.ricci x (e i) (e j) *
        (D.covariantTensorDerivative P x ![e i, e j, a, b] +
          D.covariantTensorDerivative P x ![e i, e j, b, a])) +
      (∑ i, ∑ j, hamiltonP D x (e i) (e j) a * hamiltonP D x (e i) (e j) b) -
      2 * (∑ i, ∑ j, hamiltonP D x a (e i) (e j) * hamiltonP D x b (e j) (e i)) +
      2 * (∑ i, ∑ j, ∑ k, D.ricci x (e i) (e j) * D.ricci x (e i) (e k) *
        D.curvatureTensor x a (e k) b (e j)) -
      D.ricci x a b / (2 * (t - T₀) ^ 2) := by
  have hM := tensorHeatOperator_hamiltonM_decomposition hC F T₀ ht hτ x a b
  have hP := tensorHeatOperator_divergence_hamiltonP_reaction hC F ht x a b
  have hCprod := tensorHeatOperator_curvatureRicci hC F ht x a b
  have hQ := tensorHeatOperator_ricci_timeCorrection hC F T₀ ht hτ x a b
  have hcontract := curvature_contraction_hamiltonM (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) (t - T₀) x a b
  dsimp only at hM hP hCprod hQ hcontract ⊢
  linarith only [hM, hP, hCprod, hQ, hcontract]

end Poincare.RicciFlow.Harnack
