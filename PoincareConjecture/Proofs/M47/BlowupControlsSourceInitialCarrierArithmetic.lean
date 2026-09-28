import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.M47



theorem exists_source_initial_carrier_factors
    (A0 L : ℝ) (hA0 : 0 < A0) (hL : 1200 ≤ L) :
    ∃ Lambda eta0 delta0 : ℝ,
      1 < Lambda ∧ Lambda < 1001 / 1000 ∧ 0 < eta0 ∧ 0 < delta0 ∧
      (∀ delta : ℝ, 0 ≤ delta → delta ≤ delta0 →
        Real.sqrt (1 + delta) ≤ Lambda ∧ 1 ≤ (1 - delta) * Lambda ^ 2) ∧
      (∀ eta : ℝ, eta ≤ eta0 → 1 ≤ (1 - eta) * Lambda ^ 2) ∧
      Lambda * (A0 + 5 + Lambda * (2 * L / 3)) <
        A0 + 4 + (20 / 29 : ℝ) * (L - 2) := by
  let sigma := 1 / (100 * (A0 + L + 10))
  have hden : 0 < 100 * (A0 + L + 10) := by positivity
  have hsigma : 0 < sigma := one_div_pos.mpr hden
  have hsigmaSmall : sigma < 1 / 1000 := by
    dsimp only [sigma]
    apply (div_lt_iff₀ hden).mpr
    linarith only [hA0, hL]
  have hidentity : sigma * (A0 + L + 10) = 1 / 100 := by
    dsimp only [sigma]
    field_simp
  let Lambda := 1 + sigma
  have hLambda : 1 < Lambda := by dsimp only [Lambda]; linarith
  have hLambdaSmall : Lambda < 1001 / 1000 := by
    dsimp only [Lambda]
    linarith only [hsigmaSmall]
  have hLambdaSq : 1 < Lambda ^ 2 := by nlinarith only [hLambda]
  have hLambdaSqFour : Lambda ^ 2 ≤ 4 := by
    nlinarith only [hLambda, hLambdaSmall]
  have hLambdaSqLower : 1 + 2 * sigma ≤ Lambda ^ 2 := by
    dsimp only [Lambda]
    nlinarith only [sq_nonneg sigma]
  let eta0 := (Lambda ^ 2 - 1) / (2 * Lambda ^ 2)
  let delta0 := sigma / 4
  have heta0 : 0 < eta0 := div_pos (sub_pos.mpr hLambdaSq) (by positivity)
  have hdelta0 : 0 < delta0 := div_pos hsigma (by norm_num)
  refine ⟨Lambda, eta0, delta0, hLambda, hLambdaSmall, heta0, hdelta0, ?_, ?_, ?_⟩
  · intro delta hdelta hsmall
    change delta ≤ sigma / 4 at hsmall
    have hprod : delta * Lambda ^ 2 ≤ sigma := by
      have h := mul_le_mul_of_nonneg_left hLambdaSqFour hdelta
      linarith only [h, hsmall]
    refine ⟨Real.sqrt_le_iff.mpr ⟨by linarith only [hLambda], ?_⟩, ?_⟩
    · linarith only [hsmall, hLambdaSqLower, hsigma]
    · nlinarith only [hprod, hLambdaSqLower, hsigma]
  · intro eta hsmall
    have heq : eta0 * (2 * Lambda ^ 2) = Lambda ^ 2 - 1 :=
      div_mul_cancel₀ _ (by positivity)
    have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg Lambda)
    nlinarith only [heq, hmul, hLambdaSq]
  · have hlinear : sigma * (A0 + 5) ≤ 2 * sigma * (A0 + 10) := by
      have h := mul_nonneg hsigma.le (show 0 ≤ A0 + 15 by linarith only [hA0])
      nlinarith only [h]
    have hquadratic : (2 * sigma + sigma ^ 2) * (2 * L / 3) ≤
        2 * sigma * L := by
      have hsquare : sigma ^ 2 ≤ sigma := by
        nlinarith only [hsigma, hsigmaSmall]
      have h := mul_le_mul_of_nonneg_right hsquare (show 0 ≤ 2 * L / 3 by linarith)
      nlinarith only [h]
    have herror : sigma * (A0 + 5) +
        (2 * sigma + sigma ^ 2) * (2 * L / 3) ≤ 1 / 50 := by
      calc
        _ ≤ 2 * sigma * (A0 + 10) + 2 * sigma * L := add_le_add hlinear hquadratic
        _ = 2 * (sigma * (A0 + L + 10)) := by ring
        _ = 1 / 50 := by rw [hidentity]; norm_num
    have hexpand : Lambda * (A0 + 5 + Lambda * (2 * L / 3)) =
        A0 + 5 + 2 * L / 3 + sigma * (A0 + 5) +
          (2 * sigma + sigma ^ 2) * (2 * L / 3) := by
      dsimp only [Lambda]
      ring
    rw [hexpand]
    linarith only [herror, hL]

end PoincareConjecture.M47
