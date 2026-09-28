import PoincareConjecture.Proofs.M25.AppA_1_Necks.EuclideanMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelEstimate











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem normalizedEuclideanCoefficients_lower (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ N.m25_normalizedEuclideanCoefficients q s 0 v v := by
  have he := (abs_le.mp (N.normalizedEuclideanCoefficients_quadratic_error q hs v)).1
  have hm := norm_sq_le_roundCylinderEuclideanModelCoefficients v
  have hp : 0 ≤ roundCylinderEuclideanModelCoefficients 0 v v :=
    (sq_nonneg ‖v‖).trans hm
  have hsmall := mul_le_mul_of_nonneg_right N.epsilon_lt_half.le hp
  nlinarith



theorem normalizedEuclideanCoefficients_upper (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    N.m25_normalizedEuclideanCoefficients q s 0 v v ≤ 3 * ‖v‖ ^ 2 := by
  have he := (abs_le.mp (N.normalizedEuclideanCoefficients_quadratic_error q hs v)).2
  have hlow := norm_sq_le_roundCylinderEuclideanModelCoefficients v
  have hp : 0 ≤ roundCylinderEuclideanModelCoefficients 0 v v :=
    (sq_nonneg ‖v‖).trans hlow
  have hsmall := mul_le_mul_of_nonneg_right N.epsilon_lt_half.le hp
  have hm : roundCylinderEuclideanModelCoefficients 0 v v ≤ 2 * ‖v‖ ^ 2 := by
    rw [roundCylinderEuclideanModelCoefficients_zero, RiemannianMetric.lineModelEquiv_norm_sq v]
    nlinarith [sq_nonneg (((RiemannianMetric.lineModelEquiv 2).symm v).2)]
  nlinarith



theorem exists_normalizedEuclideanCoefficients_firstJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ‖fderiv ℝ (N.m25_normalizedEuclideanCoefficients q s) 0‖ ≤ C * N.epsilon := by
  let T : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] RoundCylinderCoordinates :=
    (RiemannianMetric.lineModelEquiv 2).symm
  let P : (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
    (RiemannianMetric.parameterBilinearEquiv T).toContinuousLinearMap
  let C := 216 * max 1 ‖P‖ * max 1 ‖T.toContinuousLinearMap‖
  have hP : 0 < max 1 ‖P‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hT : 0 < max 1 ‖T.toContinuousLinearMap‖ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M _ _ _ _ _ _ g N q s hs
  have : T2Space M := inferInstance
  let phi := fun x : EuclideanSpace ℝ (Fin 3) => (0, s) + T x
  have hphi : HasFDerivAt phi T.toContinuousLinearMap 0 :=
    T.hasFDerivAt.const_add (0, s)
  have hphi0 : phi 0 = (0, s) := by simp only [phi, map_zero, add_zero]
  have hA : DifferentiableAt ℝ (N.normalizedCenteredCoefficients q) (phi 0) := by
    rw [hphi0]
    exact (N.normalizedCenteredCoefficients_contDiffAt q hs).differentiableAt (by simp)
  have hfun : (fun x : EuclideanSpace ℝ (Fin 3) =>
      P (N.normalizedCenteredCoefficients q (phi x))) =
      N.m25_normalizedEuclideanCoefficients q s := by
    funext x
    rfl
  have hder : fderiv ℝ (N.m25_normalizedEuclideanCoefficients q s) 0 =
      P.comp ((fderiv ℝ (N.normalizedCenteredCoefficients q) (0, s)).comp
        T.toContinuousLinearMap) := by
    have h := (P.hasFDerivAt.comp 0 (hA.hasFDerivAt.comp 0 hphi)).fderiv
    simpa only [Function.comp_def, hphi0, hfun] using h
  rw [hder]
  calc
    _ ≤ ‖P‖ * (‖fderiv ℝ (N.normalizedCenteredCoefficients q) (0, s)‖ *
        ‖T.toContinuousLinearMap‖) :=
      (P.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ max 1 ‖P‖ * ((216 * N.epsilon) * max 1 ‖T.toContinuousLinearMap‖) := by
      apply mul_le_mul (le_max_right _ _) ?_
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hP.le
      exact mul_le_mul (N.norm_fderiv_normalizedCenteredCoefficients_le q hs)
        (le_max_right _ _) (norm_nonneg _)
        (mul_nonneg (by norm_num) N.epsilon_pos.le)
    _ = C * N.epsilon := by dsimp [C]; ring



theorem exists_normalizedEuclideanCoefficients_christoffel_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ‖CoordinateExponential.christoffelBilinear
        (N.m25_normalizedEuclideanCoefficients q s) 0‖ ≤ K * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_normalizedEuclideanCoefficients_firstJet_bound.{u}
  refine ⟨3 * C, by positivity, ?_⟩
  intro M _ _ _ _ _ _ g N q s hs
  have h := CoordinateExponential.norm_christoffelBilinear_le_of_ellipticity
    (N.m25_normalizedEuclideanCoefficients q s) 0 (a := 1 / 2) (by norm_num)
    (N.normalizedEuclideanCoefficients_lower q hs)
  calc
    _ ≤ 3 * ‖fderiv ℝ (N.m25_normalizedEuclideanCoefficients q s) 0‖ := by norm_num at h ⊢; exact h
    _ ≤ 3 * (C * N.epsilon) := mul_le_mul_of_nonneg_left (hbound N q hs) (by norm_num)
    _ = (3 * C) * N.epsilon := by ring

end PoincareConjecture.EpsilonNeck
