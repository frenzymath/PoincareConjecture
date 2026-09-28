import PoincareConjecture.Proofs.M36.CylinderModelField
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Norm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem euclideanThree_multilinear_apply_bound {r : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin r => E₃) ℝ) {tau : ℝ} (_htau : 0 ≤ tau)
    (hT : ∀ a : Fin r → Fin 3,
      |T (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j))| ≤ tau)
    (v : Fin r → E₃) :
    |T v| ≤ (3 : ℝ) ^ r * tau * ∏ j, ‖v j‖ := by
  classical
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hrepr (a : Fin r → Fin 3) (j : Fin r) :
      |b.toBasis.repr (v j) (a j)| ≤ ‖v j‖ := by
    rw [b.coe_toBasis_repr_apply, b.repr_apply_apply]
    simpa only [Real.norm_eq_abs, b.norm_eq_one, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (b (a j)) (v j)
  rw [multilinear_apply_basis_expansion T b.toBasis v]
  calc
    _ ≤ ∑ a : Fin r → Fin 3,
        |∏ j, b.toBasis.repr (v j) (a j)| * |T (fun j => b (a j))| := by
      simpa only [abs_mul, b.coe_toBasis] using
        Finset.abs_sum_le_sum_abs
          (fun a : Fin r → Fin 3 => (∏ j, b.toBasis.repr (v j) (a j)) *
            T (fun j => b.toBasis (a j))) Finset.univ
    _ ≤ ∑ _a : Fin r → Fin 3, (∏ j, ‖v j‖) * tau := by
      apply Finset.sum_le_sum
      intro a _
      rw [Finset.abs_prod]
      apply mul_le_mul _ (hT a) (abs_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hrepr a j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

noncomputable def cylinderModelCurvature : MultilinearMap ℝ (fun _ : Fin 4 => E₃) ℝ :=
  MultilinearMap.mk'
    (fun v => 2 * (cylinderHorizontalForm (v 0) (v 2) *
      cylinderHorizontalForm (v 1) (v 3) -
      cylinderHorizontalForm (v 0) (v 3) * cylinderHorizontalForm (v 1) (v 2)))
    (by
      intro v i a b
      fin_cases i <;> simp [map_add, add_apply] <;> ring)
    (by
      intro v i c a
      fin_cases i <;> simp [map_smul, smul_apply, smul_eq_mul] <;> ring)

theorem cylinderModelCurvature_apply (v : Fin 4 → E₃) :
    cylinderModelCurvature v = 2 * (cylinderHorizontalForm (v 0) (v 2) *
      cylinderHorizontalForm (v 1) (v 3) -
      cylinderHorizontalForm (v 0) (v 3) * cylinderHorizontalForm (v 1) (v 2)) := rfl

theorem cylinderModelCurvature_plane_nonneg (v w : E₃) :
    0 ≤ cylinderModelCurvature ![v, w, v, w] := by
  change 0 ≤ 2 * (inner ℝ (cylinderHorizontalProjection v) (cylinderHorizontalProjection v) *
      inner ℝ (cylinderHorizontalProjection w) (cylinderHorizontalProjection w) -
    inner ℝ (cylinderHorizontalProjection v) (cylinderHorizontalProjection w) *
      inner ℝ (cylinderHorizontalProjection w) (cylinderHorizontalProjection v))
  rw [real_inner_comm (cylinderHorizontalProjection w) (cylinderHorizontalProjection v)]
  nlinarith only [real_inner_mul_inner_self_le
    (cylinderHorizontalProjection w) (cylinderHorizontalProjection v)]

theorem cylinderHeightCovector_sq_le_norm_sq (v : E₃) :
    cylinderHeightCovector v ^ 2 ≤ ‖v‖ ^ 2 := by
  have h := congrArg (fun A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => A v v)
    cylinderHorizontalForm_add_vertical
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at h
  rw [real_inner_self_eq_norm_sq] at h
  have hH : 0 ≤ cylinderHorizontalForm v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  nlinarith only [h, hH]

theorem cylinderModelCurvature_plane_gram (v w : E₃) :
    cylinderModelCurvature ![v, w, v, w] =
      (cylinderModelField 0 v v * cylinderModelField 0 w w -
        cylinderModelField 0 v w ^ 2 -
        cylinderHeightCovector v ^ 2 * cylinderModelField 0 w w -
        cylinderHeightCovector w ^ 2 * cylinderModelField 0 v v +
        2 * cylinderHeightCovector v * cylinderHeightCovector w *
          cylinderModelField 0 v w) / 2 := by
  have hsymm : cylinderHorizontalForm w v = cylinderHorizontalForm v w := by
    simp only [cylinderHorizontalForm_apply]
    exact real_inner_comm _ _
  change 2 * (cylinderHorizontalForm v v * cylinderHorizontalForm w w -
    cylinderHorizontalForm v w * cylinderHorizontalForm w v) = _
  rw [cylinderModelField_zero]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hsymm]
  ring

theorem cylinder_plane_gram_error {rho a b c x y : ℝ}
    (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 2)
    (ha : |a - 1| ≤ 2 * rho) (hb : |b - 1| ≤ 2 * rho) (hc : |c| ≤ 2 * rho)
    (hx : x ^ 2 ≤ 2) (hy : y ^ 2 ≤ 2) :
    |(a * b - c ^ 2 - x ^ 2 * b - y ^ 2 * a + 2 * x * y * c) / 2 -
      (1 - x ^ 2 - y ^ 2) / 2| ≤ 12 * rho := by
  have hr : (2 * rho) ^ 2 ≤ 2 * rho := by
    nlinarith only [mul_nonneg hrho (sub_nonneg.mpr hsmall)]
  have hab : |(a - 1) * (b - 1)| ≤ 2 * rho := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) (by positivity)).trans (by nlinarith only [hr])
  have hc2 : c ^ 2 ≤ 2 * rho := by
    have h := mul_le_mul hc hc (abs_nonneg c) (by positivity : 0 ≤ 2 * rho)
    simpa only [← pow_two, sq_abs] using h.trans (by nlinarith only [hr])
  have hxb : |x ^ 2 * (b - 1)| ≤ 4 * rho := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
    nlinarith only [mul_le_mul hx hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  have hya : |y ^ 2 * (a - 1)| ≤ 4 * rho := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
    nlinarith only [mul_le_mul hy ha (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  have hxy : |x * y| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hx, hy, sq_nonneg (x + y), sq_nonneg (x - y)]
  have hcross : |2 * x * y * c| ≤ 8 * rho := by
    have he : 2 * x * y * c = 2 * (x * y) * c := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := mul_le_mul hxy hc (abs_nonneg c) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [h]
  obtain ⟨haL, haU⟩ := abs_le.mp ha
  obtain ⟨hbL, hbU⟩ := abs_le.mp hb
  obtain ⟨habL, habU⟩ := abs_le.mp hab
  obtain ⟨hxbL, hxbU⟩ := abs_le.mp hxb
  obtain ⟨hyaL, hyaU⟩ := abs_le.mp hya
  obtain ⟨hcrossL, hcrossU⟩ := abs_le.mp hcross
  apply abs_le.mpr
  constructor <;> nlinarith only [haL, haU, hbL, hbU, habL, habU,
    hxbL, hxbU, hyaL, hyaU, hcrossL, hcrossU, hc2, sq_nonneg c]

theorem cylinder_close_unit_norm_sq
    (A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ) {rho : ℝ} (hsmall : rho ≤ 1 / 2)
    (hA : ‖A - cylinderModelField 0‖ ≤ rho) {v : E₃} (hv : A v v = 1) :
    ‖v‖ ^ 2 ≤ 2 := by
  have he : |A v v - cylinderModelField 0 v v| ≤ rho * ‖v‖ * ‖v‖ := by
    exact ((A - cylinderModelField 0).le_opNorm₂ v v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
        (norm_nonneg v))
  rw [hv] at he
  have hlo := (abs_le.mp he).1
  have hbound := cylinderModelField_zero_lower v
  have hr := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖v‖)
  nlinarith only [hlo, hbound, hr]

theorem cylinder_close_plane_bounds
    (A : E₃ →L[ℝ] E₃ →L[ℝ] ℝ)
    (T : MultilinearMap ℝ (fun _ : Fin 4 => E₃) ℝ)
    {rho tau : ℝ} (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 2) (htau : 0 ≤ tau)
    (hA : ‖A - cylinderModelField 0‖ ≤ rho)
    (hT : ∀ a : Fin 4 → Fin 3,
      |(T - cylinderModelCurvature) (fun j => EuclideanSpace.basisFun (Fin 3) ℝ (a j))| ≤ tau)
    (v w : E₃) (hvv : A v v = 1) (hww : A w w = 1) (hvw : A v w = 0) :
    -324 * tau ≤ T ![v, w, v, w] ∧
      |T ![v, w, v, w] -
        (1 - cylinderHeightCovector v ^ 2 - cylinderHeightCovector w ^ 2) / 2| ≤
          324 * tau + 12 * rho := by
  have hnv := cylinder_close_unit_norm_sq A hsmall hA hvv
  have hnw := cylinder_close_unit_norm_sq A hsmall hA hww
  have hprod : ‖v‖ * ‖w‖ ≤ 2 := by
    nlinarith only [hnv, hnw, sq_nonneg (‖v‖ - ‖w‖)]
  have he (u z : E₃) :
      |cylinderModelField 0 u z - A u z| ≤ rho * ‖u‖ * ‖z‖ := by
    have h := ((A - cylinderModelField 0).le_opNorm₂ u z).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (norm_nonneg u))
        (norm_nonneg z))
    simpa only [sub_apply, Real.norm_eq_abs, abs_sub_comm] using h
  have ha : |cylinderModelField 0 v v - 1| ≤ 2 * rho := by
    have h := he v v
    rw [hvv] at h
    nlinarith only [h, mul_le_mul_of_nonneg_left hnv hrho]
  have hb : |cylinderModelField 0 w w - 1| ≤ 2 * rho := by
    have h := he w w
    rw [hww] at h
    nlinarith only [h, mul_le_mul_of_nonneg_left hnw hrho]
  have hc : |cylinderModelField 0 v w| ≤ 2 * rho := by
    have h := he v w
    rw [hvw, sub_zero] at h
    nlinarith only [h, mul_le_mul_of_nonneg_left hprod hrho]
  have hm := cylinder_plane_gram_error hrho hsmall ha hb hc
    ((cylinderHeightCovector_sq_le_norm_sq v).trans hnv)
    ((cylinderHeightCovector_sq_le_norm_sq w).trans hnw)
  rw [← cylinderModelCurvature_plane_gram] at hm
  have hdiff : |T ![v, w, v, w] - cylinderModelCurvature ![v, w, v, w]| ≤
      324 * tau := by
    have h := euclideanThree_multilinear_apply_bound (T - cylinderModelCurvature)
      htau hT ![v, w, v, w]
    have h4 : ‖v‖ * ‖w‖ * ‖v‖ * ‖w‖ ≤ 4 := by
      nlinarith only [mul_le_mul hprod hprod
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Fin.prod_univ_four] at h
    change |T ![v, w, v, w] - cylinderModelCurvature ![v, w, v, w]| ≤
      81 * tau * (‖v‖ * ‖w‖ * ‖v‖ * ‖w‖) at h
    nlinarith only [h, mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 81 * tau)]
  constructor
  · have h := (abs_le.mp hdiff).1
    linarith only [h, cylinderModelCurvature_plane_nonneg v w]
  · calc
      _ ≤ |T ![v, w, v, w] - cylinderModelCurvature ![v, w, v, w]| +
          |cylinderModelCurvature ![v, w, v, w] -
            (1 - cylinderHeightCovector v ^ 2 - cylinderHeightCovector w ^ 2) / 2| :=
        abs_sub_le _ _ _
      _ ≤ _ := add_le_add hdiff hm

end PoincareConjecture.M36
