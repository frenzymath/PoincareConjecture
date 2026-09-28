import PoincareConjecture.Proofs.M34.Standard.DifferenceFluxAlgebra
import PoincareConjecture.Proofs.M03.CurvatureRateAlgebra










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy



noncomputable def modelRicciTrace {n : ℕ} (T : FS n) (u v : V n) : ℝ :=
  ∑ k : Fin n, EuclideanSpace.proj k (T (EuclideanSpace.single k 1) u v)



noncomputable def modelCurvatureReaction {n : ℕ} (I : Inverse n) (T : FS n)
    (u v w : V n) : V n :=
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  ∑ i : Fin n, ∑ j : Fin n, EuclideanSpace.proj i (I (EuclideanSpace.proj j)) •
    (T (T u v (e i)) (e j) w - (2 : ℝ) • T v (e i) (T (e j) u w) +
      (2 : ℝ) • T (e i) u (T v (e j) w) + modelRicciTrace T (T u v w) (e i) • e j -
      modelRicciTrace T u (e i) • T (e j) v w -
      modelRicciTrace T v (e i) • T u (e j) w -
      modelRicciTrace T w (e i) • T u v (e j))



noncomputable def modelCurvatureReactionDifference {n : ℕ}
    (G G' : FH n) (R R' : FS n) : Raw n := fun l j k m =>
  EuclideanSpace.proj l
    (modelCurvatureReaction G.inverse R (EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1) (EuclideanSpace.single m 1) -
    modelCurvatureReaction G'.inverse R' (EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1) (EuclideanSpace.single m 1))



theorem exists_uniform_modelCurvatureReaction_energy_bound {n dH dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G G' : FH n), G.IsInvertible → G'.IsInvertible →
      ∀ (R R' : FS n), ‖G.inverse‖ ≤ M → ‖G'.inverse‖ ≤ M → ‖R‖ ≤ M → ‖R'‖ ≤ M →
        (∑ alpha : Fin dS, 2 * qS (R - R') alpha *
          curvatureContraction qS (modelCurvatureReactionDifference G G' R R') alpha) ≤
          C * ((∑ i, qH (G - G') i ^ 2) + (∑ i, qS (R - R') i ^ 2)) := by
  classical
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let B : Fin n → Fin n → Fin n → Fin n → FS n := fun l j k m =>
    (EuclideanSpace.proj j).smulRight ((EuclideanSpace.proj k).smulRight
      ((EuclideanSpace.proj m).smulRight (e l)))
  let theta := fun alpha : Fin dS => ∑ l, ∑ j, ∑ k, ∑ m, |qS (B l j k m) alpha|
  let T := ∑ alpha, theta alpha
  let C0 := (n : ℝ) ^ 2 * (5 + 4 * n) *
    (M ^ 4 * ‖qH.symm.toContinuousLinearMap‖ +
      2 * M ^ 2 * ‖qS.symm.toContinuousLinearMap‖)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have htheta (alpha : Fin dS) : 0 ≤ theta alpha := by dsimp [theta]; positivity
  have hT : 0 ≤ T := Finset.sum_nonneg (fun alpha _ => htheta alpha)
  refine ⟨3 * T * C0, by positivity, fun G G' hG hG' R R' hI hI' hR hR' => ?_⟩
  let h := qH (G - G')
  let s := qS (R - R')
  have hh : ‖G - G'‖ ≤ ‖qH.symm.toContinuousLinearMap‖ * ‖h‖ := by
    simpa only [h, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
      using qH.symm.toContinuousLinearMap.le_opNorm h
  have hs : ‖R - R'‖ ≤ ‖qS.symm.toContinuousLinearMap‖ * ‖s‖ := by
    simpa only [s, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
      using qS.symm.toContinuousLinearMap.le_opNorm s
  have he (i : Fin n) : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
  have hraw (l j k m : Fin n) : |modelCurvatureReactionDifference G G' R R' l j k m| ≤
      C0 * (‖h‖ + ‖s‖) := by
    have hr := Proofs.M03.norm_model_curvature_reaction_difference_le G G' hG hG' R R'
      (e j) (e k) (e m)
    change ‖modelCurvatureReaction G.inverse R (e j) (e k) (e m) -
      modelCurvatureReaction G'.inverse R' (e j) (e k) (e m)‖ ≤ _ at hr
    simp only [he, mul_one] at hr
    have hc := PiLp.norm_apply_le
      (modelCurvatureReaction G.inverse R (e j) (e k) (e m) -
        modelCurvatureReaction G'.inverse R' (e j) (e k) (e m)) l
    rw [Real.norm_eq_abs] at hc
    refine (hc.trans hr).trans ?_
    calc
      _ ≤ (n : ℝ) ^ 2 * (5 + 4 * n) *
          (M * (‖qH.symm.toContinuousLinearMap‖ * ‖h‖) * M * M ^ 2 +
            M * (M + M) * (‖qS.symm.toContinuousLinearMap‖ * ‖s‖)) := by gcongr
      _ ≤ C0 * (‖h‖ + ‖s‖) := by
        dsimp only [C0]
        nlinarith only [mul_nonneg
          (show 0 ≤ (n : ℝ) ^ 2 * (5 + 4 * n) * M ^ 4 *
            ‖qH.symm.toContinuousLinearMap‖ by positivity) (norm_nonneg s),
          mul_nonneg (show 0 ≤ (n : ℝ) ^ 2 * (5 + 4 * n) * 2 * M ^ 2 *
            ‖qS.symm.toContinuousLinearMap‖ by positivity) (norm_nonneg h)]
  have hq (alpha : Fin dS) :
      |curvatureContraction qS (modelCurvatureReactionDifference G G' R R') alpha| ≤
        theta alpha * (C0 * (‖h‖ + ‖s‖)) := by
    dsimp only [curvatureContraction, LinearMap.coe_mk, AddHom.coe_mk, theta, B, e]
    simp only [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro l _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro k _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro m _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hraw l j k m) (abs_nonneg _)
  have hpoint (alpha : Fin dS) :
      2 * s alpha * curvatureContraction qS (modelCurvatureReactionDifference G G' R R') alpha ≤
        2 * ‖s‖ * (theta alpha * (C0 * (‖h‖ + ‖s‖))) := by
    have hsc : |s alpha| ≤ ‖s‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le s alpha
    calc
      _ ≤ |2 * s alpha *
        curvatureContraction qS (modelCurvatureReactionDifference G G' R R') alpha| :=
          le_abs_self _
      _ = 2 * |s alpha| *
          |curvatureContraction qS (modelCurvatureReactionDifference G G' R R') alpha| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ _ := by gcongr; exact hq alpha
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun alpha _ => hpoint alpha)
  have hright : (∑ alpha : Fin dS, 2 * ‖s‖ * (theta alpha * (C0 * (‖h‖ + ‖s‖)))) =
      T * C0 * (2 * ‖s‖ * (‖h‖ + ‖s‖)) := by
    dsimp only [T]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro alpha _
    ring
  rw [hright] at hsum
  have hyoung : 2 * ‖s‖ * (‖h‖ + ‖s‖) ≤ 3 * (‖h‖ ^ 2 + ‖s‖ ^ 2) := by
    nlinarith [sq_nonneg (‖h‖ - ‖s‖), sq_nonneg ‖h‖]
  have hfinal := hsum.trans (mul_le_mul_of_nonneg_left hyoung (mul_nonneg hT hC0))
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hfinal
  change _ ≤ 3 * T * C0 * ((∑ i, h i ^ 2) + (∑ i, s i ^ 2))
  nlinarith only [hfinal]

end PoincareConjecture.M34.DifferenceEnergy
