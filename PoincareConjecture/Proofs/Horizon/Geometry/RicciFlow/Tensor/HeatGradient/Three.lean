import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative.General
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.Laplacian.Three
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MetricDuality
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.RicciAction.Three

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

lemma covariantTensorDerivative_fixed_heat_commutator_three
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {T W : ℝ → CovariantTensorEvaluation n M 3} {t : ℝ} (ht : t ∈ interior J)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X : Fin 3 → (z : M) → TangentSpace (𝓡 n) z),
      (∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) y) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, y))
    (hW : ∀ (y : M) (z : Fin 3 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    deriv (fun s => (F.connection s).covariantTensorDerivative (T s) x ![a, b, c, d]) t -
        D.tensorLaplacian (D.covariantTensorDerivative (T t)) x ![a, b, c, d] -
        (D.covariantTensorDerivative (W t) x ![a, b, c, d] -
          D.covariantTensorDerivative (D.tensorLaplacian (T t)) x ![a, b, c, d]) =
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative (T t) x ![e i, e j, c, d]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) c (e j) *
        D.covariantTensorDerivative (T t) x ![e i, b, e j, d]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) d (e j) *
        D.covariantTensorDerivative (T t) x ![e i, b, c, e j]) -
      (∑ i, D.ricci x a (e i) * D.covariantTensorDerivative (T t) x ![e i, b, c, d]) +
      (∑ j, D.covariantTensorDerivative D.ricciEvaluation x ![a, b, e j] * T t x ![e j, c, d]) +
      (∑ j, D.covariantTensorDerivative D.ricciEvaluation x ![a, c, e j] * T t x ![b, e j, d]) +
      (∑ j, D.covariantTensorDerivative D.ricciEvaluation x ![a, d, e j] * T t x ![b, c, e j]) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D := F.connection t
  let e := (F.metric t).orthonormalBasis x
  let A := fun q : TangentSpace (𝓡 n) x => deriv (fun s =>
    (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) q) x) t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have htime := (F.hasDerivAt_covariantTensorDerivative_time_all ht x hT hreg hW a ![b, c, d]).deriv
  have hlap := D.covariantTensorDerivative_tensorLaplacian_commutator_three hD (hT t) x a b c d
  have hslot (r : Fin 3) : T t x (Function.update ![b, c, d] r (A (![b, c, d] r) a)) =
      ∑ j, (-D.covariantTensorDerivative D.ricciEvaluation x ![a, ![b, c, d] r, e j] -
        D.covariantTensorDerivative D.ricciEvaluation x ![![b, c, d] r, a, e j] +
        D.covariantTensorDerivative D.ricciEvaluation x ![e j, a, ![b, c, d] r]) *
          T t x (Function.update ![b, c, d] r (e j)) := by
    rw [(hT t).update_eq_sum (F.metric t) x ![b, c, d] r (A (![b, c, d] r) a)]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact F.inner_deriv_connection_extend ht hD x a (![b, c, d] r) (e j)
  have hup (w : TangentSpace (𝓡 n) x) :
      Function.update ![b, c, d] 0 w = ![w, c, d] ∧
      Function.update ![b, c, d] 1 w = ![b, w, d] ∧
      Function.update ![b, c, d] 2 w = ![b, c, w] := by
    constructor
    · ext i; fin_cases i <;> simp
    constructor <;> (ext i; fin_cases i <;> simp)
  change _ = D.covariantTensorDerivative (W t) x ![a, b, c, d] -
    ∑ r : Fin 3, T t x (Function.update ![b, c, d] r (A (![b, c, d] r) a)) at htime
  simp_rw [hslot] at htime
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    hup, sub_mul, add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib] at htime
  dsimp only at hlap ⊢
  simp only [sub_mul, Finset.sum_sub_distrib] at hlap
  dsimp only [D, e] at htime hlap
  simp only [Matrix.Fin.cons_vecCons, Matrix.head_cons, Matrix.tail_cons] at htime
  linarith only [htime, hlap]

lemma tensorHeatOperator_covariantTensorDerivative_commutator_three
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {T W : ℝ → CovariantTensorEvaluation n M 3} {t : ℝ} (ht : t ∈ interior J)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X : Fin 3 → (z : M) → TangentSpace (𝓡 n) z),
      (∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) y) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, y))
    (hW : ∀ (y : M) (z : Fin 3 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    tensorHeatOperator F (fun s => (F.connection s).covariantTensorDerivative (T s)) t x ![a, b, c, d] -
      D.covariantTensorDerivative (tensorHeatOperator F T t) x ![a, b, c, d] =
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative (T t) x ![e i, e j, c, d]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) c (e j) *
        D.covariantTensorDerivative (T t) x ![e i, b, e j, d]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) d (e j) *
        D.covariantTensorDerivative (T t) x ![e i, b, c, e j]) := by
  let D := F.connection t
  let e := (F.metric t).orthonormalBasis x
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hWs := isSmoothCovariantTensor_timeDerivative_all hT hreg hW
  have hLs : IsSmoothCovariantTensor (D.tensorLaplacian (T t)) :=
    (hD.2.2.1 _ _ (hD.2.2.1 _ _ (hT t))).tensorTrace
  have hAs := D.isSmoothCovariantTensor_ricciTensorAction_three hD (hT t)
  have hheat : tensorHeatOperator F T t = fun y z =>
      W t y z + D.ricciTensorAction (T t) y z - D.tensorLaplacian (T t) y z := by
    funext y z
    exact congrArg (fun q => q + D.ricciTensorAction (T t) y z -
      D.tensorLaplacian (T t) y z) (hW y z).deriv
  have hder : D.covariantTensorDerivative (tensorHeatOperator F T t) x ![a, b, c, d] =
      D.covariantTensorDerivative (W t) x ![a, b, c, d] +
        D.covariantTensorDerivative (D.ricciTensorAction (T t)) x ![a, b, c, d] -
        D.covariantTensorDerivative (D.tensorLaplacian (T t)) x ![a, b, c, d] := by
    rw [hheat, D.covariantTensorDerivative_sub (hWs.add hAs) hLs,
      D.covariantTensorDerivative_add hWs hAs]
  have hfix := F.covariantTensorDerivative_fixed_heat_commutator_three hC ht hT hreg hW x a b c d
  have hric := D.covariantTensorDerivative_ricciTensorAction_three hD (hT t) x a ![b, c, d]
  have hup3 (w : TangentSpace (𝓡 n) x) :
      Function.update ![b, c, d] 0 w = ![w, c, d] ∧
      Function.update ![b, c, d] 1 w = ![b, w, d] ∧
      Function.update ![b, c, d] 2 w = ![b, c, w] := by
    constructor
    · ext i; fin_cases i <;> simp
    constructor <;> (ext i; fin_cases i <;> simp)
  have hup4 (w : TangentSpace (𝓡 n) x) :
      Function.update ![a, b, c, d] 0 w = ![w, b, c, d] ∧
      Function.update ![a, b, c, d] 1 w = ![a, w, c, d] ∧
      Function.update ![a, b, c, d] 2 w = ![a, b, w, d] ∧
      Function.update ![a, b, c, d] 3 w = ![a, b, c, w] := by
    constructor
    · ext i; fin_cases i <;> simp
    constructor
    · ext i; fin_cases i <;> simp
    constructor <;> (ext i; fin_cases i <;> simp)
  have hact : D.ricciTensorAction (D.covariantTensorDerivative (T t)) x ![a, b, c, d] =
      (∑ i, D.ricci x a (e i) * D.covariantTensorDerivative (T t) x ![e i, b, c, d]) +
      (∑ i, D.ricci x b (e i) * D.covariantTensorDerivative (T t) x ![a, e i, c, d]) +
      (∑ i, D.ricci x c (e i) * D.covariantTensorDerivative (T t) x ![a, b, e i, d]) +
      (∑ i, D.ricci x d (e i) * D.covariantTensorDerivative (T t) x ![a, b, c, e i]) := by
    unfold LeviCivitaData.ricciTensorAction
    rw [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, hup4]
    rfl
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, hup3, Matrix.Fin.cons_vecCons, Finset.sum_add_distrib] at hric
  dsimp only at hfix ⊢
  change deriv (fun s => (F.connection s).covariantTensorDerivative (T s) x ![a, b, c, d]) t +
    D.ricciTensorAction (D.covariantTensorDerivative (T t)) x ![a, b, c, d] -
    D.tensorLaplacian (D.covariantTensorDerivative (T t)) x ![a, b, c, d] -
    D.covariantTensorDerivative (tensorHeatOperator F T t) x ![a, b, c, d] = _
  rw [hder, hact]
  dsimp only [D, e] at hric ⊢
  simp only [Matrix.head_cons, Matrix.tail_cons] at hric
  linarith only [hfix, hric]

end PoincareConjecture.RicciFlow
