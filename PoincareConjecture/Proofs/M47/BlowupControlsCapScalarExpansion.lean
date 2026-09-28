import PoincareConjecture.Proofs.M47.BlowupControlsCapRicciFrame
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarContraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "V" => EuclideanSpace ℝ I

theorem cap_scalar_difference_expansion_normal
    {g0 g1 : RiemannianMetric 3 V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (e : V ≃L[ℝ] V) (x : V)
    (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0) :
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
    D1.scalarCurvature x - D0.scalarCurvature x =
      (∑ i, ∑ j, (A i j - A0 i j) * D0.ricci x (e (b i)) (e (b j))) +
      (∑ i, ∑ j, ∑ k, ∑ l, (A i j * A k l / 2) *
        (Z k i j l + Z k j i l - Z k l i j - Z i k j l - Z i j k l + Z i l k j)) +
      ((1 / 2 : ℝ) *
        ((∑ i, ∑ j, ∑ k, ∑ l, A i j * U k k l * S l i j) -
          (∑ i, ∑ j, ∑ k, ∑ l, A i j * U i k l * S l k j)) +
        ((∑ i, ∑ j, ∑ k, ∑ l, A i j * B k k l * B l i j) -
          (∑ i, ∑ j, ∑ k, ∑ l, A i j * B k i l * B l k j))) := by
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
  let Delta := fun u v y => D1.euclideanConnection u v y - D0.euclideanConnection u v y
  let B := fun k i j => inner ℝ (b k) (e.symm (Delta (e (b i)) (e (b j)) x))
  let dB := fun l k i j =>
    inner ℝ (b k) (e.symm (fderiv ℝ (Delta (e (b i)) (e (b j))) x (e (b l))))
  have hd (w k i j : I) : dB w k i j = (1 / 2 : ℝ) * ∑ l,
      (U w k l * S l i j + A k l * (Z w i j l + Z w j i l - Z w l i j)) :=
    cap_connectionDifference_fderiv_normal D0 D1 e x hzero (e (b i)) (e (b j)) (e (b w)) k
  have hr (i j : I) : D1.ricci x (e (b i)) (e (b j)) - D0.ricci x (e (b i)) (e (b j)) =
      ∑ k, ((dB k k i j - dB i k k j) + ∑ l, (B k k l * B l i j - B k i l * B l k j)) :=
    cap_ricci_difference_connection_frame D0 D1 e x hzero i j
  have hexpand :
      (∑ i, ∑ j, A i j * (D1.ricci x (e (b i)) (e (b j)) - D0.ricci x (e (b i)) (e (b j)))) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        ((A i j * A k l / 2) *
          (Z k i j l + Z k j i l - Z k l i j - Z i k j l - Z i j k l + Z i l k j) +
          (1 / 2 : ℝ) * (A i j * U k k l * S l i j - A i j * U i k l * S l k j) +
          (A i j * B k k l * B l i j - A i j * B k i l * B l k j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hd, hd]
    simp only [mul_add, mul_sub, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hsplit :
      (∑ i, ∑ j, ∑ k, ∑ l,
        ((A i j * A k l / 2) *
          (Z k i j l + Z k j i l - Z k l i j - Z i k j l - Z i j k l + Z i l k j) +
          (1 / 2 : ℝ) * (A i j * U k k l * S l i j - A i j * U i k l * S l k j) +
          (A i j * B k k l * B l i j - A i j * B k i l * B l k j))) =
      (∑ i, ∑ j, ∑ k, ∑ l, (A i j * A k l / 2) *
        (Z k i j l + Z k j i l - Z k l i j - Z i k j l - Z i j k l + Z i l k j)) +
      ((1 / 2 : ℝ) *
        ((∑ i, ∑ j, ∑ k, ∑ l, A i j * U k k l * S l i j) -
          (∑ i, ∑ j, ∑ k, ∑ l, A i j * U i k l * S l k j)) +
        ((∑ i, ∑ j, ∑ k, ∑ l, A i j * B k k l * B l i j) -
          (∑ i, ∑ j, ∑ k, ∑ l, A i j * B k i l * B l k j))) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hs := cap_scalar_difference_frame D0 D1 x e
  change D1.scalarCurvature x - D0.scalarCurvature x =
    (∑ i, ∑ j, (A i j - A0 i j) * D0.ricci x (e (b i)) (e (b j))) +
      ∑ i, ∑ j, A i j * (D1.ricci x (e (b i)) (e (b j)) - D0.ricci x (e (b i)) (e (b j))) at hs
  rw [hexpand, hsplit] at hs
  change D1.scalarCurvature x - D0.scalarCurvature x =
    (∑ i, ∑ j, (A i j - A0 i j) * D0.ricci x (e (b i)) (e (b j))) + _ + _
  exact hs.trans (add_assoc _ _ _).symm

end PoincareConjecture.M47
