import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Spacetime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.P
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative.General
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem hasDerivAt_divergence_hamiltonP
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let Pdot : CovariantTensorEvaluation n M 3 := fun y z =>
      deriv (fun s => hamiltonP (F.connection s) y (z 0) (z 1) (z 2)) t
    let A := fun z : TangentSpace (𝓡 n) x => deriv (fun s =>
      (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) t
    HasDerivAt
      (fun s => (F.metric s).tensorTrace ((F.connection s).covariantTensorDerivative
        (fun y z => hamiltonP (F.connection s) y (z 0) (z 1) (z 2))) x ![u, v])
      ((∑ i, (D.covariantTensorDerivative Pdot x ![b i, b i, u, v] -
          (hamiltonP D x (A (b i) (b i)) u v +
            hamiltonP D x (b i) (A u (b i)) v +
            hamiltonP D x (b i) u (A v (b i))))) +
        2 * ∑ i, ∑ j, D.ricci x (b i) (b j) *
          D.covariantTensorDerivative
            (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![b i, b j, u, v]) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let T : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
    hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
  let W : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
    deriv (fun r => T r y z) s
  let A := fun (y : M) (z : TangentSpace (𝓡 n) y) => deriv (fun s =>
    (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) y) t
  let Q : ℝ → CovariantTensorEvaluation n M 4 := fun _ y z =>
    (F.connection t).covariantTensorDerivative (W t) y z -
      ∑ i : Fin 3, T t y (Function.update (fun j => z j.succ) i (A y (z i.succ) (z 0)))
  have hT (s) := hamiltonP_isSmoothCovariantTensor (F.connection s)
    (hC.tensor_calculus n M (F.metric s) (F.connection s))
  have hreg (y : M) (X : Fin 3 → (z : M) → TangentSpace (𝓡 n) z)
      (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) y) := contMDiffAt_hamiltonP_fields hC F ht hX
  have hW (y : M) (z : Fin 3 → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s => T s y z) (W t y z) t :=
    (hasDerivAt_hamiltonP_evolution hC F ht y (z 0) (z 1) (z 2)).differentiableAt.hasDerivAt
  have hQ (z : Fin 4 → TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s => (F.connection s).covariantTensorDerivative (T s) x z)
        (Q t x z) t := by
    have h := F.hasDerivAt_covariantTensorDerivative_time_all ht x hT hreg hW
      (z 0) (fun i => z i.succ)
    have heq : Fin.cons (z 0) (fun i : Fin 3 => z i.succ) = z := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    simpa only [heq, Q, A] using h
  have h := F.hasDerivAt_tensorTrace (T := fun s =>
      (F.connection s).covariantTensorDerivative (T s)) (W := Q) ht x
    (fun s => (hC.tensor_calculus n M (F.metric s) (F.connection s)).2.2.1 _ _ (hT s))
    hQ ![u, v]
  convert h using 1
  simp only [RiemannianMetric.tensorTrace, Q, Fin.sum_univ_three,
    Matrix.Fin.cons_vecCons, Matrix.cons_val_zero, T, W, A]
  rfl

theorem tensorHeatOperator_divergence_hamiltonP_commutator
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
      hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
    F.tensorHeatOperator (fun s => (F.metric s).tensorTrace
        ((F.connection s).covariantTensorDerivative (P s))) t x ![u, v] -
      (F.metric t).tensorTrace (D.covariantTensorDerivative (F.tensorHeatOperator P t)) x ![u, v] =
      2 * (∑ i, ∑ j, D.ricci x (e i) (e j) *
        D.covariantTensorDerivative (P t) x ![e i, e j, u, v]) +
      2 * (∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) u (e j) *
        D.covariantTensorDerivative (P t) x ![e i, e k, e j, v]) +
      2 * (∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) v (e j) *
        D.covariantTensorDerivative (P t) x ![e i, e k, u, e j]) := by
  let D := F.connection t
  let e := (F.metric t).orthonormalBasis x
  let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
    hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
  let W : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
    deriv (fun r => P r y z) s
  let Q : ℝ → CovariantTensorEvaluation n M 4 := fun s =>
    (F.connection s).covariantTensorDerivative (P s)
  let Qdot : ℝ → CovariantTensorEvaluation n M 4 := fun s y z =>
    deriv (fun r => Q r y z) s
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hP (s) := hamiltonP_isSmoothCovariantTensor (F.connection s)
    (hC.tensor_calculus n M (F.metric s) (F.connection s))
  have hreg (y : M) (X : Fin 3 → (z : M) → TangentSpace (𝓡 n) z)
      (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) y) := contMDiffAt_hamiltonP_fields hC F ht hX
  have hW (y : M) (z : Fin 3 → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s => P s y z) (W t y z) t :=
    (hasDerivAt_hamiltonP_evolution hC F ht y (z 0) (z 1) (z 2)).differentiableAt.hasDerivAt
  have hQ (s) : IsSmoothCovariantTensor (Q s) :=
    (hC.tensor_calculus n M (F.metric s) (F.connection s)).2.2.1 _ _ (hP s)
  have hQdot (y : M) (z : Fin 4 → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s => Q s y z) (Qdot t y z) t := by
    have h := F.hasDerivAt_covariantTensorDerivative_time_all ht y hP hreg hW
      (z 0) (fun i => z i.succ)
    have hz : Fin.cons (z 0) (fun i : Fin 3 => z i.succ) = z := by
      ext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hz] at h
    exact h.differentiableAt.hasDerivAt
  have htrace := F.tensorHeatOperator_tensorTrace_four hC ht hQ hQdot x u v
  have hcurv (i j) : (∑ k, D.curvatureTensor x (e k) (e i) (e k) (e j)) =
      D.ricci x (e i) (e j) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [(hD.2.2.2.1 x (e k) (e i) (e k) (e j)).2.1,
      (hD.2.2.2.1 x (e k) (e j) (e k) (e i)).1,
      (hD.2.2.2.1 x (e k) (e j) (e i) (e k)).2.1,
      (hD.2.2.2.1 x (e i) (e k) (e k) (e j)).1, neg_neg]
  have hfirst : (∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) (e k) (e j) *
        Q t x ![e i, e j, u, v]) =
      ∑ i, ∑ j, D.ricci x (e i) (e j) * Q t x ![e i, e j, u, v] := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, hcurv]
  dsimp only
  change F.tensorHeatOperator (fun s => (F.metric s).tensorTrace (Q s)) t x ![u, v] -
    (F.metric t).tensorTrace (D.covariantTensorDerivative (F.tensorHeatOperator P t)) x ![u, v] = _
  rw [htrace]
  change (∑ i, F.tensorHeatOperator Q t x ![e i, e i, u, v]) -
    (∑ i, D.covariantTensorDerivative (F.tensorHeatOperator P t) x ![e i, e i, u, v]) = _
  rw [← Finset.sum_sub_distrib]
  have hgrad (i) := tensorHeatOperator_covariantHamiltonP_commutator hC F ht x (e i) (e i) u v
  change ∀ i, F.tensorHeatOperator Q t x ![e i, e i, u, v] -
    D.covariantTensorDerivative (F.tensorHeatOperator P t) x ![e i, e i, u, v] = _ at hgrad
  simp_rw [hgrad]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  dsimp only [D, e, Q, P] at hfirst
  rw [hfirst]

theorem tensorHeatOperator_divergence_hamiltonP
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
      hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
    F.tensorHeatOperator (fun s => (F.metric s).tensorTrace
        ((F.connection s).covariantTensorDerivative (P s))) t x ![u, v] =
      (F.metric t).tensorTrace (D.covariantTensorDerivative (hamiltonPReaction D)) x ![u, v] +
      2 * (∑ i, ∑ j, D.ricci x (e i) (e j) *
        D.covariantTensorDerivative (P t) x ![e i, e j, u, v]) +
      2 * (∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) u (e j) *
        D.covariantTensorDerivative (P t) x ![e i, e k, e j, v]) +
      2 * (∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) v (e j) *
        D.covariantTensorDerivative (P t) x ![e i, e k, u, e j]) := by
  have h := tensorHeatOperator_divergence_hamiltonP_commutator hC F ht x u v
  dsimp only at h ⊢
  rw [tensorHeatOperator_hamiltonP hC F ht] at h
  linarith only [h]

end Poincare.RicciFlow.Harnack
