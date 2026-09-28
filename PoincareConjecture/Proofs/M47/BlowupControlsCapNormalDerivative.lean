import PoincareConjecture.Proofs.M47.BlowupControlsCapNativeDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem normal_constant_field_smooth (v : V) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x : V => Bundle.TotalSpace.mk' V x (E := TangentSpace (𝓡 n)) v) univ := by
  intro x _
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩

theorem cap_tensorEvaluation_contDiff {r : ℕ}
    (T : CovariantTensorEvaluation n V r) (hT : IsSmoothCovariantTensor T)
    (v : Fin r → V) : ContDiff ℝ ∞ (fun y => T y v) := by
  have h := hT.2 univ isOpen_univ (fun i _ => v i)
    (fun i => normal_constant_field_smooth (v i))
  exact contMDiff_iff_contDiff.mp (contMDiffOn_univ.mp h)

theorem cap_covariantTensorDerivative_normal
    {g : RiemannianMetric n V} (D : LeviCivitaData g) {r : ℕ}
    (T : CovariantTensorEvaluation n V r) (hT : IsSmoothCovariantTensor T)
    (x : V) (hzero : ∀ u v : V, D.euclideanConnection u v x = 0)
    (v : Fin (r + 1) → V) :
    D.covariantTensorDerivative T x v =
      fderiv ℝ (fun y => T y (fun i => v i.succ)) x (v 0) := by
  let X : Fin (r + 1) → (y : V) → TangentSpace (𝓡 n) y := fun i _ => v i
  have h := M04.covariantTensorDerivativeOnFields_eq D hT isOpen_univ
    (fun i => normal_constant_field_smooth (v i)) (mem_univ x)
  change M04.covariantTensorDerivativeOnFields D T X x =
    D.covariantTensorDerivative T x v at h
  rw [← h]
  unfold M04.covariantTensorDerivativeOnFields
  simp only [X, mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
  have hz (i : Fin r) : D.connection (fun _ : V => v i.succ) x (v 0) = 0 :=
    hzero (v 0) (v i.succ)
  simp only [hz]
  obtain ⟨A, hA⟩ := hT.1 x
  simp only [hA, A.map_update_zero, Finset.sum_const_zero, sub_zero]
  rfl

theorem cap_metric_fderiv_normal
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0)
    (x : V) (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0)
    (u v w : V) :
    let H : CovariantTensorEvaluation n V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    fderiv ℝ (fun y => g1.inner y v w) x u =
      D0.covariantTensorDerivative H x ![u, v, w] := by
  let H : CovariantTensorEvaluation n V 2 :=
    fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
  have hmetric (g : RiemannianMetric n V) :
      DifferentiableAt ℝ (fun y => g.inner y v w) x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have h := (normal_constant_field_smooth v).inner_bundle
      (normal_constant_field_smooth w)
    exact mdifferentiableAt_iff_differentiableAt.mp
      ((h.contMDiffAt (by simp)).mdifferentiableAt (by simp))
  have hpair := M04.metric_derivative_pairing D0 (fun _ : V => u) (x := x)
    (((normal_constant_field_smooth v).contMDiffAt (by simp)).mdifferentiableAt (by simp))
    (((normal_constant_field_smooth w).contMDiffAt (by simp)).mdifferentiableAt (by simp))
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at hpair
  change fderiv ℝ (fun y => g0.inner y v w) x u =
    g0.inner x (D0.euclideanConnection u v x) w +
      g0.inner x v (D0.euclideanConnection u w x) at hpair
  simp only [hzero, map_zero, zero_apply, zero_add] at hpair
  change _ = D0.covariantTensorDerivative H x ![u, v, w]
  rw [cap_covariantTensorDerivative_normal D0 H (cap_metricDifference_smooth g0 g1)
    x hzero]
  change _ = fderiv ℝ (fun y => g1.inner y v w - g0.inner y v w) x u
  rw [fderiv_fun_sub (hmetric g1) (hmetric g0), sub_apply, hpair, sub_zero]

theorem cap_secondCovariantTensorDerivative_normal
    {g : RiemannianMetric n V} (D : LeviCivitaData g) {r : ℕ}
    (T : CovariantTensorEvaluation n V r) (hT : IsSmoothCovariantTensor T)
    (x : V) (hzero : ∀ u v : V, D.euclideanConnection u v x = 0)
    (v : Fin (r + 1) → V) (u : V) :
    fderiv ℝ (fun y => D.covariantTensorDerivative T y v) x u =
      D.covariantTensorDerivative (D.covariantTensorDerivative T) x (Fin.cons u v) := by
  symm
  exact cap_covariantTensorDerivative_normal D (D.covariantTensorDerivative T)
    (M04.isSmoothCovariantTensor_covariantTensorDerivative D hT) x hzero (Fin.cons u v)

end PoincareConjecture.M47
