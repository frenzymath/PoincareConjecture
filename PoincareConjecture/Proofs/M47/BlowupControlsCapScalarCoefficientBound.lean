import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarExpansion
import PoincareConjecture.Proofs.M47.BlowupControlsCapHessianPairing
import PoincareConjecture.Proofs.M47.BlowupControlsCapQuadraticContraction
import PoincareConjecture.Proofs.M47.BlowupControlsCapKoszulBounds
import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseTensorBounds
import PoincareConjecture.Proofs.M47.BlowupControlsCapFrameError










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "V" => EuclideanSpace ℝ I
local notation "Idx" => Fin 4 → I



theorem cap_scalar_difference_coefficient_bound
    {g0 g1 : RiemannianMetric 3 V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (e : V ≃L[ℝ] V) (x : V)
    (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0) :
    let b := EuclideanSpace.basisFun I ℝ
    let H : CovariantTensorEvaluation 3 V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    let A0 := M04.frameInverseGram g0 x e.toContinuousLinearMap
    let A := M04.frameInverseGram g1 x e.toContinuousLinearMap
    let P := fun i j k => D0.covariantTensorDerivative H x ![e (b i), e (b j), e (b k)]
    let Z := fun i j k l => D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x
      ![e (b i), e (b j), e (b k), e (b l)]
    let a := ‖(M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse‖
    |D1.scalarCurvature x - D0.scalarCurvature x| ≤
      ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2 - A0 p.1 p.2) :
        EuclideanSpace ℝ (I × I))‖ *
        ‖(WithLp.toLp 2 (fun p : I × I => D0.ricci x (e (b p.1)) (e (b p.2))) :
          EuclideanSpace ℝ (I × I))‖ +
      ‖capScalarHessianComponents (WithLp.toLp 2 (fun p : I × I => A p.1 p.2))‖ *
        ‖(WithLp.toLp 2 (fun v : Idx => Z (v 0) (v 1) (v 2) (v 3)) :
          EuclideanSpace ℝ Idx)‖ +
      18 * a ^ 3 * ‖capThreeTensorComponents P‖ ^ 2 := by
  let b := EuclideanSpace.basisFun I ℝ
  let H : CovariantTensorEvaluation 3 V 2 :=
    fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
  let A0 := M04.frameInverseGram g0 x e.toContinuousLinearMap
  let A := M04.frameInverseGram g1 x e.toContinuousLinearMap
  let P := fun i j k => D0.covariantTensorDerivative H x ![e (b i), e (b j), e (b k)]
  let S := fun k i j => P i j k + P j i k - P k i j
  let Z := fun i j k l => D0.covariantTensorDerivative (D0.covariantTensorDerivative H) x
    ![e (b i), e (b j), e (b k), e (b l)]
  let U := fun i j k => fderiv ℝ
    (fun y => M04.frameInverseGram g1 y e.toContinuousLinearMap j k) x (e (b i))
  let B := fun k i j => inner ℝ (b k) (e.symm
    (D1.euclideanConnection (e (b i)) (e (b j)) x -
      D0.euclideanConnection (e (b i)) (e (b j)) x))
  let Ai := (M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse
  let a := ‖Ai‖
  let q0 := ∑ i, ∑ j, (A i j - A0 i j) * D0.ricci x (e (b i)) (e (b j))
  let qH := ∑ i, ∑ j, ∑ k, ∑ l, (A i j * A k l / 2) *
    (Z k i j l + Z k j i l - Z k l i j - Z i k j l - Z i j k l + Z i l k j)
  let qQ := (1 / 2 : ℝ) *
    ((∑ i, ∑ j, ∑ k, ∑ l, A i j * U k k l * S l i j) -
      (∑ i, ∑ j, ∑ k, ∑ l, A i j * U i k l * S l k j)) +
    ((∑ i, ∑ j, ∑ k, ∑ l, A i j * B k k l * B l i j) -
      (∑ i, ∑ j, ∑ k, ∑ l, A i j * B k i l * B l k j))
  have hq0 : |q0| ≤
      ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2 - A0 p.1 p.2) :
        EuclideanSpace ℝ (I × I))‖ *
      ‖(WithLp.toLp 2 (fun p : I × I => D0.ricci x (e (b p.1)) (e (b p.2))) :
        EuclideanSpace ℝ (I × I))‖ := by
    simpa only [Fintype.sum_prod_type] using cap_array_pairing_abs_le
      (fun p : I × I => A p.1 p.2 - A0 p.1 p.2)
      (fun p : I × I => D0.ricci x (e (b p.1)) (e (b p.2)))
  have hAsym (i j : I) : A i j = A j i := cap_frameInverseGram_symm g1 x e i j
  have hZsym (i j k l : I) : Z i j l k = Z i j k l :=
    cap_metricDifference_hessian_symm_normal D0 x hzero (e (b i)) (e (b j))
      (e (b l)) (e (b k))
  have hqH : |qH| ≤
      ‖capScalarHessianComponents (WithLp.toLp 2 (fun p : I × I => A p.1 p.2))‖ *
        ‖(WithLp.toLp 2 (fun v : Idx => Z (v 0) (v 1) (v 2) (v 3)) :
          EuclideanSpace ℝ Idx)‖ := cap_hessian_scalar_pairing_le A hAsym Z hZsym
  have hA : ‖(WithLp.toLp 2 (fun p : I × I => A p.1 p.2) :
      EuclideanSpace ℝ (I × I))‖ ≤ Real.sqrt 3 * a := cap_operatorComponents_norm_le Ai
  have hU : ‖capThreeTensorComponents U‖ ≤ a ^ 2 * ‖capThreeTensorComponents P‖ :=
    cap_inverseDerivative_tensor_norm_le D0 e x hzero (norm_nonneg Ai) le_rfl
  have hS : ‖capThreeTensorComponents S‖ ≤ 3 * ‖capThreeTensorComponents P‖ :=
    cap_koszul_array_norm_le P
  have hB : ‖capThreeTensorComponents B‖ ≤ (3 / 2 : ℝ) * a * ‖capThreeTensorComponents P‖ :=
    cap_connectionDifference_components_norm_le D0 D1 e x
  have hqQ : |qQ| ≤ 18 * a ^ 3 * ‖capThreeTensorComponents P‖ ^ 2 :=
    cap_quadratic_scalar_contraction_le A U S B (norm_nonneg Ai) (norm_nonneg _)
      hA hU hS hB
  have hexact : D1.scalarCurvature x - D0.scalarCurvature x = q0 + qH + qQ :=
    cap_scalar_difference_expansion_normal D0 D1 e x hzero
  rw [hexact]
  exact ((abs_add_le (q0 + qH) qQ).trans
    (add_le_add (abs_add_le q0 qH) le_rfl)).trans (add_le_add (add_le_add hq0 hqH) hqQ)

end PoincareConjecture.M47
