import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.ProductDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.RicciDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Algebra
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def ricciTensorAction (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (x : M)
    (v : Fin k → TangentSpace (𝓡 n) x) : ℝ :=
  ∑ j, ∑ i, D.ricci x (v j) (g.orthonormalBasis x i) *
    T x (Function.update v j (g.orthonormalBasis x i))

lemma ricciTensorAction_two (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 2) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.ricciTensorAction T x ![u, v] =
      ∑ i, (D.ricci x u (g.orthonormalBasis x i) *
          T x ![g.orthonormalBasis x i, v] +
        D.ricci x v (g.orthonormalBasis x i) *
          T x ![u, g.orthonormalBasis x i]) := by
  simp only [ricciTensorAction, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have h0 : Function.update ![u, v] 0 (g.orthonormalBasis x i) =
      ![g.orthonormalBasis x i, v] := by ext j; fin_cases j <;> simp
    rw [h0]
  · apply Finset.sum_congr rfl
    intro i hi
    have h1 : Function.update ![u, v] 1 (g.orthonormalBasis x i) =
        ![u, g.orthonormalBasis x i] := by ext j; fin_cases j <;> simp
    rw [h1]

lemma ricciTensorAction_three (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.ricciTensorAction T x ![u, v, w] =
      ∑ j, ∑ i, D.ricci x (![u, v, w] j) (g.orthonormalBasis x i) *
        T x (Function.update ![u, v, w] j (g.orthonormalBasis x i)) := by
  rfl

lemma isSmoothCovariantTensor_ricciTensorAction_two
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.ricciTensorAction T) := by
  let L : CovariantTensorEvaluation n M 2 := fun y z =>
    ∑ i, D.ricci y (z 0) (g.orthonormalBasis y i) *
      T y ![g.orthonormalBasis y i, z 1]
  let R : CovariantTensorEvaluation n M 2 := fun y z =>
    ∑ i, T y ![z 0, g.orthonormalBasis y i] *
      D.ricci y (g.orthonormalBasis y i) (z 1)
  have hL : IsSmoothCovariantTensor L :=
    D.isSmoothCovariantTensor_tensorProduct_trace_order_two hD.2.1 hT
  have hR : IsSmoothCovariantTensor R :=
    D.isSmoothCovariantTensor_tensorProduct_trace_order_two hT hD.2.1
  have heq : D.ricciTensorAction T = fun y z => L y z + R y z := by
    funext y z
    have hz : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
    rw [← hz]
    have hh := D.ricciTensorAction_two T y (z 0) (z 1)
    rw [Finset.sum_add_distrib] at hh
    rw [hh]
    dsimp [L, R]
    conv_lhs => rw [← Finset.sum_add_distrib]
    conv_rhs => rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hs := (hD.2.2.2.1 y (g.orthonormalBasis y i) (z 1)
      (g.orthonormalBasis y i) (z 1)).2.2.2
    rw [hs]
    ring
  rw [heq]
  exact hL.add hR

lemma covariantTensorDerivative_ricciTensorAction_two
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.ricciTensorAction T) x ![u, v, w] =
      ∑ i, (D.covariantTensorDerivative D.ricciEvaluation x ![u, v,
          g.orthonormalBasis x i] * T x ![g.orthonormalBasis x i, w] +
        D.ricci x v (g.orthonormalBasis x i) *
          D.covariantTensorDerivative T x ![u, g.orthonormalBasis x i, w] +
        D.covariantTensorDerivative D.ricciEvaluation x ![u, w,
          g.orthonormalBasis x i] * T x ![v, g.orthonormalBasis x i] +
        D.ricci x w (g.orthonormalBasis x i) *
          D.covariantTensorDerivative T x ![u, v, g.orthonormalBasis x i]) := by
  let L : CovariantTensorEvaluation n M 2 := fun y z =>
    ∑ i, D.ricci y (z 0) (g.orthonormalBasis y i) *
      T y ![g.orthonormalBasis y i, z 1]
  let R : CovariantTensorEvaluation n M 2 := fun y z =>
    ∑ i, T y ![z 0, g.orthonormalBasis y i] *
      D.ricci y (g.orthonormalBasis y i) (z 1)
  have heq : D.ricciTensorAction T = fun y z => L y z + R y z := by
    funext y z
    have hz : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
    rw [← hz]
    have hh := D.ricciTensorAction_two T y (z 0) (z 1)
    rw [Finset.sum_add_distrib] at hh
    rw [hh]
    dsimp [L, R]
    conv_lhs => rw [← Finset.sum_add_distrib]
    conv_rhs => rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hs := (hD.2.2.2.1 y (g.orthonormalBasis y i) (z 1)
      (g.orthonormalBasis y i) (z 1)).2.2.2
    rw [hs]
    ring
  rw [heq]
  have hLs := D.isSmoothCovariantTensor_tensorProduct_trace_order_two hD.2.1 hT
  have hRs := D.isSmoothCovariantTensor_tensorProduct_trace_order_two hT hD.2.1
  dsimp only [L, R]
  have hLs' : IsSmoothCovariantTensor (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) =>
      ∑ i, D.ricci y (z 0) (g.orthonormalBasis y i) *
        T y ![g.orthonormalBasis y i, z 1]) := by
    simpa only [ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one] using hLs
  have hRs' : IsSmoothCovariantTensor (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) =>
      ∑ i, T y ![z 0, g.orthonormalBasis y i] *
        D.ricci y (g.orthonormalBasis y i) (z 1)) := by
    simpa only [ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one] using hRs
  rw [D.covariantTensorDerivative_add hLs' hRs']
  dsimp only
  have hL := D.covariantTensorDerivative_tensorProduct_trace_order_two hD.2.1 hT x u v w
  have hR := D.covariantTensorDerivative_tensorProduct_trace_order_two hT hD.2.1 x u v w
  simp only [ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one] at hL hR
  rw [hL, hR]
  simp_rw [D.covariantTensorDerivative_ricciEvaluation_symm hD]
  have hs (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.covariantTensorDerivative D.ricciEvaluation x
          ![u, g.orthonormalBasis x i, w] =
        D.covariantTensorDerivative D.ricciEvaluation x
          ![u, w, g.orthonormalBasis x i] :=
    D.covariantTensorDerivative_ricciEvaluation_symm hD x u
      (g.orthonormalBasis x i) w
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hr : D.ricci x (g.orthonormalBasis x i) w =
      D.ricci x w (g.orthonormalBasis x i) :=
    (hD.2.2.2.1 x (g.orthonormalBasis x i) w u v).2.2.2
  rw [hr]
  ring

end PoincareConjecture.LeviCivitaData
