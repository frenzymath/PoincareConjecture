import PoincareConjecture.Proofs.M35.Uniqueness.VectorHeatEnergy
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation:max "V" n:max => EuclideanSpace ℝ (Fin n)

noncomputable def killingCovector {n : ℕ} (g : RiemannianMetric n (V n))
    (X : V n → V n) : CovariantTensorEvaluation n (V n) 1 :=
  fun x v => g.inner x (X x) (v 0)

theorem isSmoothCovariantTensor_killingCovector {n : ℕ}
    (g : RiemannianMetric n (V n)) (X : V n → V n) (hX : ContDiff ℝ ∞ X) :
    IsSmoothCovariantTensor (killingCovector g X) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine ⟨fun x => ⟨MultilinearMap.ofSubsingleton ℝ (TangentSpace (𝓡 n) x) ℝ (0 : Fin 1)
    (g.inner x (X x)).toLinearMap, fun _ => rfl⟩, ?_⟩
  intro U _ Y hY
  exact (euclidean_field_contMDiff hX).contMDiffOn.inner_bundle (hY 0)

theorem killingCovector_derivative {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (hX : ContDiff ℝ ∞ X)
    (x : V n) (v : Fin 2 → V n) :
    D.covariantTensorDerivative (killingCovector g X) x v =
      g.inner x (D.connection X x (v 0)) (v 1) := by
  have hS := euclidean_field_contMDiff hX
  have hC (a : V n) := euclidean_field_contMDiff (contDiff_const (c := a) :
    ContDiff ℝ ∞ (fun _ : V n => a))
  have he := M04.covariantTensorDerivativeOnFields_eq D
    (isSmoothCovariantTensor_killingCovector g X hX) isOpen_univ
    (X := fun i _ => v i) (fun i => (hC (v i)).contMDiffOn) (x := x) (mem_univ x)
  rw [← he]
  simp only [M04.covariantTensorDerivativeOnFields, killingCovector, Fin.sum_univ_one,
    Function.update_self]
  change mvfderiv (𝓡 n) (fun y => g.inner y (X y) (v 1)) x (v 0) -
    g.inner x (X x) (D.connection (fun _ => v 1) x (v 0)) = _
  rw [D.mvfderiv_inner (fun _ => v 0) X (fun _ => v 1)
    ((hS x).mdifferentiableAt (by simp)) ((hC (v 1) x).mdifferentiableAt (by simp))]
  ring

theorem killingCovector_second_derivative {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (hX : ContDiff ℝ ∞ X)
    (x : V n) (v : Fin 3 → V n) :
    D.covariantTensorDerivative (D.covariantTensorDerivative (killingCovector g X)) x v =
      g.inner x (fieldHessian D X x (v 0) (v 1)) (v 2) := by
  have hS := euclidean_field_contMDiff hX
  have hC (a : V n) := euclidean_field_contMDiff (contDiff_const (c := a) :
    ContDiff ℝ ∞ (fun _ : V n => a))
  have hN (a : V n) : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => Bundle.TotalSpace.mk' (V n) y (E := TangentSpace (𝓡 n))
        (D.connection X y a)) := by
    rw [← contMDiffOn_univ]
    exact D.contMDiffOn_connection_apply isOpen_univ (fun _ => a) X
      (hC a).contMDiffOn hS.contMDiffOn
  have he := M04.covariantTensorDerivativeOnFields_eq D
    (M04.isSmoothCovariantTensor_covariantTensorDerivative D
      (isSmoothCovariantTensor_killingCovector g X hX)) isOpen_univ
    (X := fun i _ => v i) (fun i => (hC (v i)).contMDiffOn) (x := x) (mem_univ x)
  rw [← he]
  simp only [M04.covariantTensorDerivativeOnFields, killingCovector_derivative D X hX,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change mvfderiv (𝓡 n) (fun y => g.inner y (D.connection X y (v 1)) (v 2)) x (v 0) -
    (g.inner x (D.connection X x (D.connection (fun _ => v 1) x (v 0))) (v 2) +
      g.inner x (D.connection X x (v 1)) (D.connection (fun _ => v 2) x (v 0))) = _
  rw [D.mvfderiv_inner (fun _ => v 0) (fun y => D.connection X y (v 1)) (fun _ => v 2)
    ((hN (v 1) x).mdifferentiableAt (by simp))
    ((hC (v 2) x).mdifferentiableAt (by simp))]
  simp only [fieldHessian, map_sub, sub_apply]
  ring

theorem killingCovector_laplacian {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (hX : ContDiff ℝ ∞ X)
    (x : V n) (v : Fin 1 → V n) :
    D.tensorLaplacian (killingCovector g X) x v =
      g.inner x (∑ i, fieldHessian D X x
        (g.orthonormalBasis x i) (g.orthonormalBasis x i)) (v 0) := by
  simp only [LeviCivitaData.tensorLaplacian, LeviCivitaData.iteratedCovariantTensorDerivative,
    killingCovector_second_derivative D X hX, map_sum, sum_apply]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

theorem killing_defect_eq_covector_symmetrization {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X) (x u v : V n) :
    DeTurckNative.metricLieDerivative D X x u v =
      D.covariantTensorDerivative (killingCovector g X) x ![u, v] +
        D.covariantTensorDerivative (killingCovector g X) x ![v, u] := by
  rw [DeTurckNative.metricLieDerivative_apply, killingCovector_derivative D X hX,
    killingCovector_derivative D X hX]
  exact congrArg (fun z => g.inner x (D.connection X x u) v + z)
    (g.symm x u (D.connection X x v))

end PoincareConjecture.M35.Uniqueness
