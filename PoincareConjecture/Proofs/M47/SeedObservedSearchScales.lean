import PoincareConjecture.Proofs.M47.SeedObservedSearchBounds









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

open M46



theorem exists_seed_observed_search_scales
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants) :
    ∃ B sigma lambda : ℝ, seedAnalyticConstant S ≤ B ∧ 1 ≤ B ∧
      0 < sigma ∧ 0 < lambda ∧ lambda ≤ 1 / 8 ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∀ H : ℝ, 0 < H → rNext⁻¹ ^ 2 ≤ H →
        let d := sigma / H
        let r := lambda / Real.sqrt H
        0 < d ∧ 0 < r ∧ (Real.sqrt H)⁻¹ ≤ 1 / 200 ∧
          64 * B * H * d ≤ 1 ∧ 312 * H * d ≤ 1 / 2 ∧
          r ≤ p.setup.epsilon ∧ H * r ^ 2 ≤ 1 ∧ r ^ 2 ≤ d ∧
          52 * H ≤ (r / 2)⁻¹ ^ 2 ∧ r ≤ rNext ∧ d ≤ rNext ^ 2 / 624 := by
  let B := max 1 (seedAnalyticConstant S)
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let sigma := min (1 / (128 * B)) (1 / 624)
  have hsigma : 0 < sigma := by dsimp only [sigma]; positivity
  have hsigmaScalar : sigma * (128 * B) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 128 * B)).mp (min_le_left _ _)
  have hsigmaMetric : sigma ≤ 1 / 624 := min_le_right _ _
  let lambda := min (Real.sqrt sigma) (1 / 8)
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hlambdaSmall : lambda ≤ 1 / 8 := min_le_right _ _
  have hlambdaSq : lambda ^ 2 ≤ sigma := by
    have h := (sq_le_sq₀ hlambda.le (Real.sqrt_nonneg sigma)).mpr
      (show lambda ≤ Real.sqrt sigma from min_le_left _ _)
    simpa only [Real.sq_sqrt hsigma.le] using h
  have hlambdaSqSmall : lambda ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
    (sq_le_sq₀ hlambda.le (by norm_num)).mpr hlambdaSmall
  refine ⟨B, sigma, lambda, le_max_right _ _, hB, hsigma, hlambda, hlambdaSmall, ?_⟩
  intro rNext hrNext hrLast H hH hlevel
  dsimp only
  let d := sigma / H
  let r := lambda / Real.sqrt H
  have hroot : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hd : 0 < d := div_pos hsigma hH
  have hr : 0 < r := div_pos hlambda hroot
  have hscale : 1 ≤ H * rNext ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hlevel (sq_nonneg rNext)
    have hcancel : rNext⁻¹ ^ 2 * rNext ^ 2 = 1 := by field_simp
    rwa [hcancel] at h
  have hinvH : 1 / H ≤ rNext ^ 2 := by
    apply (div_le_iff₀ hH).mpr
    nlinarith only [hscale]
  have hrootInv : (Real.sqrt H)⁻¹ ≤ rNext := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hroot).mpr
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (mul_pos hrNext hroot).le).mp
    rw [mul_pow, Real.sq_sqrt hH.le]
    nlinarith only [hscale]
  have hNextSmall : rNext ≤ 1 / 200 := hrLast.trans
    ((p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _)))
  have hrNext : r ≤ rNext := by
    calc
      r = lambda * (Real.sqrt H)⁻¹ := div_eq_mul_inv _ _
      _ ≤ 1 * rNext := mul_le_mul (by linarith only [hlambdaSmall]) hrootInv
        (inv_pos.mpr hroot).le (by norm_num)
      _ = rNext := one_mul _
  have hrSquare : r ^ 2 = lambda ^ 2 / H := by
    dsimp only [r]
    rw [div_pow, Real.sq_sqrt hH.le]
  have hHr : H * r ^ 2 = lambda ^ 2 := by rw [hrSquare]; field_simp
  have hScalar : 64 * B * H * d ≤ 1 := by
    have heq : 64 * B * H * d = 64 * B * sigma := by dsimp only [d]; field_simp
    rw [heq]
    nlinarith only [hsigmaScalar]
  have hMetric : 312 * H * d ≤ 1 / 2 := by
    have heq : 312 * H * d = 312 * sigma := by dsimp only [d]; field_simp
    rw [heq]
    linarith only [hsigmaMetric]
  have hrd : r ^ 2 ≤ d := by
    rw [hrSquare]
    exact div_le_div_of_nonneg_right hlambdaSq hH.le
  have htest : 52 * H ≤ (r / 2)⁻¹ ^ 2 := by
    rw [inv_pow, inv_eq_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos (half_pos hr))).mpr
    nlinarith only [hHr, hlambdaSqSmall]
  have hdNext : d ≤ rNext ^ 2 / 624 := by
    calc
      d = sigma * (1 / H) := by dsimp only [d]; ring
      _ ≤ (1 / 624) * (rNext ^ 2) :=
        mul_le_mul hsigmaMetric hinvH (by positivity) (by norm_num)
      _ = _ := by ring
  exact ⟨hd, hr, hrootInv.trans hNextSmall, hScalar, hMetric,
    hrNext.trans (hrLast.trans (p.r_le_epsilon _)), by nlinarith only [hHr, hlambdaSqSmall],
    hrd, htest, hrNext, hdNext⟩

end PoincareConjecture.Proofs.M47
