import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.KoszulPairing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeFields











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem connection_difference_pairing
    {g0 g1 : RiemannianMetric n M} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    {X Y Z : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) :
    let H : CovariantTensorEvaluation n M 2 :=
      fun y v ↦ g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
    2 * g1.inner x (D1.connection Y x (X x) - D0.connection Y x (X x)) (Z x) =
      covariantTensorDerivativeOnFields D0 H ![X, Y, Z] x +
      covariantTensorDerivativeOnFields D0 H ![Y, X, Z] x -
      covariantTensorDerivativeOnFields D0 H ![Z, X, Y] x := by
  let H : CovariantTensorEvaluation n M 2 :=
    fun y v ↦ g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  let A (P Q : (y : M) → TangentSpace (𝓡 n) y) :=
    D1.connection Q x (P x) - D0.connection Q x (P x)
  change 2 * g1.inner x (A X Y) (Z x) =
    covariantTensorDerivativeOnFields D0 H ![X, Y, Z] x +
    covariantTensorDerivativeOnFields D0 H ![Y, X, Z] x -
    covariantTensorDerivativeOnFields D0 H ![Z, X, Y] x
  have hsym {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% P) x)
      (hQ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% Q) x) : A P Q = A Q P := by
    apply sub_eq_zero.mp
    calc
      A P Q - A Q P =
          (D1.connection Q x (P x) - D1.connection P x (Q x)) -
          (D0.connection Q x (P x) - D0.connection P x (Q x)) := by
        dsimp only [A]
        abel
      _ = 0 := by rw [connection_commutator D1 hP hQ,
        connection_commutator D0 hP hQ, sub_self]
  have hpair (g : RiemannianMetric n M) {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% P) x)
      (hQ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% Q) x) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ g.inner y (P y) (Q y)) x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact hP.inner_bundle hQ
  have hC (P : (y : M) → TangentSpace (𝓡 n) y)
      {Q R : (y : M) → TangentSpace (𝓡 n) y}
      (hQ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% Q) x)
      (hR : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% R) x) :
      covariantTensorDerivativeOnFields D0 H ![P, Q, R] x =
        g1.inner x (A P Q) (R x) + g1.inner x (Q x) (A P R) := by
    simp only [covariantTensorDerivativeOnFields, Fin.sum_univ_succ]
    change mvfderiv (𝓡 n)
        (fun y ↦ g1.inner y (Q y) (R y) - g0.inner y (Q y) (R y)) x (P x) -
      ((g1.inner x (D0.connection Q x (P x)) (R x) -
          g0.inner x (D0.connection Q x (P x)) (R x)) +
        ((g1.inner x (Q x) (D0.connection R x (P x)) -
          g0.inner x (Q x) (D0.connection R x (P x))) + 0)) = _
    erw [mvfderiv_sub (hpair g1 hQ hR) (hpair g0 hQ hR)]
    simp only [sub_apply]
    rw [metric_derivative_pairing D1 P hQ hR, metric_derivative_pairing D0 P hQ hR]
    simp only [A, map_sub, sub_apply]
    ring
  rw [hC X hY hZ, hC Y hX hZ, hC Z hX hY,
    hsym hY hX, hsym hZ hX, hsym hZ hY,
    g1.symm x (Y x) (A X Z)]
  ring

end PoincareConjecture.RicciFlowAnalysis
