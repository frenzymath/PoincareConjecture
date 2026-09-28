import PoincareConjecture.Proofs.M47.BlowupControlsCapNormalDerivative









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem symmetry_constant_field_smooth (v : V) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x : V => Bundle.TotalSpace.mk' V x (E := TangentSpace (𝓡 n)) v) univ := by
  intro x _
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩

private theorem tensor_two_derivative
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n V 2) (hT : IsSmoothCovariantTensor T)
    (x u v w : V) :
    D.covariantTensorDerivative T x ![u, v, w] =
      fderiv ℝ (fun y => T y ![v, w]) x u -
        (T x ![D.euclideanConnection u v x, w] +
          T x ![v, D.euclideanConnection u w x]) := by
  let X : Fin 3 → (y : V) → TangentSpace (𝓡 n) y := fun i _ => ![u, v, w] i
  have h := M04.covariantTensorDerivativeOnFields_eq D hT isOpen_univ
    (fun i => symmetry_constant_field_smooth (![u, v, w] i)) (mem_univ x)
  change M04.covariantTensorDerivativeOnFields D T X x =
    D.covariantTensorDerivative T x ![u, v, w] at h
  rw [← h]
  unfold M04.covariantTensorDerivativeOnFields
  simp only [X, mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    Fin.sum_univ_two]
  change fderiv ℝ (fun y => T y ![v, w]) x u -
      (T x (Function.update ![v, w] 0 (D.euclideanConnection u v x)) +
        T x (Function.update ![v, w] 1 (D.euclideanConnection u w x))) = _
  have h0 : Function.update ![v, w] 0 (D.euclideanConnection u v x) =
      ![D.euclideanConnection u v x, w] := by
    ext i
    fin_cases i <;> simp
  have h1 : Function.update ![v, w] 1 (D.euclideanConnection u w x) =
      ![v, D.euclideanConnection u w x] := by
    ext i
    fin_cases i <;> simp
  rw [h0, h1]



theorem cap_metricDifference_derivative_symm
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0)
    (x u v w : V) :
    let H : CovariantTensorEvaluation n V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    D0.covariantTensorDerivative H x ![u, v, w] =
      D0.covariantTensorDerivative H x ![u, w, v] := by
  let H : CovariantTensorEvaluation n V 2 :=
    fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
  have hs (y a b : V) : H y ![a, b] = H y ![b, a] := by
    exact congrArg₂ (fun p q : ℝ => p - q) (g1.symm y a b) (g0.symm y a b)
  change D0.covariantTensorDerivative H x ![u, v, w] = _
  rw [tensor_two_derivative D0 H (cap_metricDifference_smooth g0 g1),
    tensor_two_derivative D0 H (cap_metricDifference_smooth g0 g1)]
  have heq : (fun y => H y ![v, w]) = fun y => H y ![w, v] :=
    funext fun y => hs y v w
  rw [heq, hs x (D0.euclideanConnection u v x) w,
    hs x v (D0.euclideanConnection u w x)]
  ring



theorem cap_metricDifference_hessian_symm_normal
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0)
    (x : V) (hzero : ∀ a b : V, D0.euclideanConnection a b x = 0)
    (u v w z : V) :
    let H : CovariantTensorEvaluation n V 2 :=
      fun y a => g1.inner y (a 0) (a 1) - g0.inner y (a 0) (a 1)
    D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x ![u, v, w, z] =
      D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x ![u, v, z, w] := by
  let H : CovariantTensorEvaluation n V 2 :=
    fun y a => g1.inner y (a 0) (a 1) - g0.inner y (a 0) (a 1)
  have heq : (fun y => D0.covariantTensorDerivative H y ![v, w, z]) =
      fun y => D0.covariantTensorDerivative H y ![v, z, w] := by
    funext y
    exact cap_metricDifference_derivative_symm D0 y v w z
  have h := congrArg (fun f : V → ℝ => fderiv ℝ f x u) heq
  calc
    _ = fderiv ℝ (fun y => D0.covariantTensorDerivative H y ![v, w, z]) x u :=
      (cap_secondCovariantTensorDerivative_normal D0 H
        (cap_metricDifference_smooth g0 g1) x hzero ![v, w, z] u).symm
    _ = fderiv ℝ (fun y => D0.covariantTensorDerivative H y ![v, z, w]) x u := h
    _ = _ := cap_secondCovariantTensorDerivative_normal D0 H
      (cap_metricDifference_smooth g0 g1) x hzero ![v, z, w] u

end PoincareConjecture.M47
