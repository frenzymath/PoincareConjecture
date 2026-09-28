import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.ReactionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Ricci
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Riemann
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatTrace.Six
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private noncomputable def curvatureRicciPerm : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective ![4, 2, 5, 0, 3, 1] (by decide)

private lemma sum_heat_product {ι : Type*} [Fintype ι]
    (r q B : ι → ι → ℝ) (s : ι → ι → ι → ι → ℝ) (G : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, (2 * B i j * q i j + r i j * (2 * ∑ k, ∑ l, s i j k l) -
      2 * ∑ k, G k i j)) =
    2 * (∑ i, ∑ j, ∑ k, ∑ l, r i j * s i j k l) -
      2 * (∑ k, ∑ i, ∑ j, G k i j) + 2 * (∑ i, ∑ j, q i j * B i j) := by
  have hG : (∑ i, ∑ j, ∑ k, G k i j) = ∑ k, ∑ i, ∑ j, G k i j := by
    calc
      _ = ∑ i, ∑ k, ∑ j, G k i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [show ∀ i j, 2 * B i j * q i j = 2 * (q i j * B i j) by intros; ring,
    show ∀ i j, r i j * (2 * ∑ k, ∑ l, s i j k l) =
      2 * (∑ k, ∑ l, r i j * s i j k l) by
        intros; simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _; ring,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hG]
  ring








lemma tensorHeatOperator_curvatureRicci
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (a b : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    F.tensorHeatOperator (fun s y z =>
      ∑ i, ∑ j, (F.connection s).curvatureTensor y (z 0)
        ((F.metric s).orthonormalBasis y i) (z 1) ((F.metric s).orthonormalBasis y j) *
        (F.connection s).ricci y ((F.metric s).orthonormalBasis y i)
          ((F.metric s).orthonormalBasis y j)) t x ![a, b] =
      2 * (∑ i, ∑ j, ∑ k, ∑ l,
        D.curvatureTensor x a (e i) b (e j) *
          D.curvatureTensor x (e i) (e k) (e j) (e l) * D.ricci x (e k) (e l)) -
      2 * (∑ k, ∑ i, ∑ j,
        D.covariantTensorDerivative D.riemannEvaluation x ![e k, a, e i, b, e j] *
          D.covariantTensorDerivative D.ricciEvaluation x ![e k, e i, e j]) +
      2 * (∑ i, ∑ j, D.ricci x (e i) (e j) *
        (D.curvatureB x (e i) a (e j) b - D.curvatureB x (e i) a b (e j) +
          D.curvatureB x (e i) (e j) a b - D.curvatureB x (e i) b a (e j))) := by
  classical
  let D := F.connection t
  let e := (F.metric t).orthonormalBasis x
  let R : ℝ → CovariantTensorEvaluation n M 4 := fun s => (F.connection s).riemannEvaluation
  let S : ℝ → CovariantTensorEvaluation n M 2 := fun s => (F.connection s).ricciEvaluation
  let U : ℝ → CovariantTensorEvaluation n M 6 := fun s y z =>
    tensorProduct (R s) (S s) y (z ∘ curvatureRicciPerm)
  have hD (s : ℝ) := hC.tensor_calculus n M (F.metric s) (F.connection s)
  have hR (y : M) (z : Fin 4 → TangentSpace (𝓡 n) y) :
      DifferentiableAt ℝ (fun s => R s y z) t :=
    ((hC.curvature_evolution n M J F t (interior_subset ht) y (z 0) (z 1) (z 2) (z 3)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).differentiableAt
  have hS (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y) :
      DifferentiableAt ℝ (fun s => S s y z) t :=
    ((hC.ricci_evolution n M J F t (interior_subset ht) y (z 0) (z 1)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).differentiableAt
  have hU (s : ℝ) : IsSmoothCovariantTensor (U s) :=
    (isSmoothCovariantTensor_tensorProduct (hD s).1 (hD s).2.1).perm curvatureRicciPerm
  have hUt (y : M) (z : Fin 6 → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s => U s y z) (deriv (fun s => U s y z) t) t :=
    ((hR y _).mul (hS y _)).hasDerivAt
  have hVt (y : M) (z : Fin 4 → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s => (F.metric s).tensorTrace (U s) y z)
        (deriv (fun s => (F.metric s).tensorTrace (U s) y z) t) t :=
    (F.hasDerivAt_tensorTrace (W := fun s y z => deriv (fun r => U r y z) s)
      ht y hU (hUt y) z).differentiableAt.hasDerivAt
  have htrace : (fun s y z =>
      ∑ i, ∑ j, (F.connection s).curvatureTensor y (z 0)
        ((F.metric s).orthonormalBasis y i) (z 1) ((F.metric s).orthonormalBasis y j) *
        (F.connection s).ricci y ((F.metric s).orthonormalBasis y i)
          ((F.metric s).orthonormalBasis y j)) =
      (fun s => (F.metric s).tensorTrace ((F.metric s).tensorTrace (U s))) := by
    rfl
  dsimp only
  rw [htrace, F.tensorHeatOperator_tensorTrace_four hC ht
    (fun s => (hU s).tensorTrace)
    (W := fun s y z => deriv (fun r => (F.metric r).tensorTrace (U r) y z) s) hVt]
  change (∑ i, F.tensorHeatOperator (fun s => (F.metric s).tensorTrace (U s))
    t x ![e i,e i,a,b]) = _
  simp_rw [F.tensorHeatOperator_tensorTrace_six hC ht hU
    (W := fun s y z => deriv (fun r => U r y z) s) hUt]
  change (∑ i, ∑ j, F.tensorHeatOperator U t x ![e j,e j,e i,e i,a,b]) = _
  have hheat (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      F.tensorHeatOperator U t x ![e j,e j,e i,e i,a,b] =
        F.tensorHeatOperator R t x ![a,e i,b,e j] * S t x ![e i,e j] +
        R t x ![a,e i,b,e j] * F.tensorHeatOperator S t x ![e i,e j] -
        2 * ∑ k, D.covariantTensorDerivative (R t) x ![e k,a,e i,b,e j] *
          D.covariantTensorDerivative (S t) x ![e k,e i,e j] := by
    rw [F.tensorHeatOperator_reindex]
    have hv : ![e j,e j,e i,e i,a,b] ∘ curvatureRicciPerm =
        ![a,e i,b,e j,e i,e j] := by
      ext k; fin_cases k <;> rfl
    rw [hv]
    exact F.tensorHeatOperator_tensorProduct_four_two (hD t).1 (hD t).2.1
      ((hD t).2.2.1 _ _ (hD t).1) ((hD t).2.2.1 _ _ (hD t).2.1) hR hS x _ _ _ _ _ _
  simp_rw [hheat]
  dsimp only [R, S]
  simp_rw [F.tensorHeatOperator_riemann hC ht, F.tensorHeatOperator_ricci hC ht]
  dsimp only [R, S, LeviCivitaData.riemannEvaluation, LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  have hB (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.curvatureB x a (e i) b (e j) - D.curvatureB x a (e i) (e j) b -
        D.curvatureB x a (e j) (e i) b + D.curvatureB x a b (e i) (e j) =
      D.curvatureB x (e i) a (e j) b - D.curvatureB x (e i) a b (e j) +
        D.curvatureB x (e i) (e j) a b - D.curvatureB x (e i) b a (e j) := by
    rw [D.curvatureB_swap_pairs (hD t) x a (e i) b (e j),
      D.curvatureB_swap_pairs (hD t) x a (e i) (e j) b,
      D.curvatureB_pair_symm x a (e j) (e i) b,
      D.curvatureB_pair_symm x a b (e i) (e j)]
    ring
  change (∑ i, ∑ j, (
    2 * (D.curvatureB x a (e i) b (e j) - D.curvatureB x a (e i) (e j) b -
      D.curvatureB x a (e j) (e i) b + D.curvatureB x a b (e i) (e j)) *
      D.ricci x (e i) (e j) +
    D.curvatureTensor x a (e i) b (e j) *
      (2 * ∑ k, ∑ l, D.curvatureTensor x (e i) (e k) (e j) (e l) * D.ricci x (e k) (e l)) -
    2 * ∑ k, D.covariantTensorDerivative D.riemannEvaluation x ![e k,a,e i,b,e j] *
      D.covariantTensorDerivative D.ricciEvaluation x ![e k,e i,e j])) = _
  simp_rw [hB]
  convert sum_heat_product
    (fun i j => D.curvatureTensor x a (e i) b (e j))
    (fun i j => D.ricci x (e i) (e j))
    (fun i j => D.curvatureB x (e i) a (e j) b - D.curvatureB x (e i) a b (e j) +
      D.curvatureB x (e i) (e j) a b - D.curvatureB x (e i) b a (e j))
    (fun i j k l => D.curvatureTensor x (e i) (e k) (e j) (e l) * D.ricci x (e k) (e l))
    (fun k i j => D.covariantTensorDerivative D.riemannEvaluation x ![e k,a,e i,b,e j] *
      D.covariantTensorDerivative D.ricciEvaluation x ![e k,e i,e j]) using 1
  simp only [D, e, mul_assoc]

end Poincare.RicciFlow.Harnack
