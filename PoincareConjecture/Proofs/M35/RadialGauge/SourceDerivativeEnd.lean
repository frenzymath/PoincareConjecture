import PoincareConjecture.Proofs.M35.RadialGauge.SourceDerivativeDifference










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem gaugeSource_weighted_fderiv_tame_bound
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ} {x : V}
    {eta B B1 L : ℝ}
    (hb : DifferentiableAt ℝ b x) (hu : DifferentiableAt ℝ u x)
    (hdu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hG : DifferentiableAt ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x))
    (hbb : ‖b x‖ ≤ B) (hdb : ‖fderiv ℝ b x‖ ≤ B1)
    (hub : (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ eta)
    (hGs : |forcingScalarDeriv G x (u x)| ≤ L) :
    (1 + ‖x‖) * ‖fderiv ℝ (gaugeSource b G u) x‖ ≤
      (B + 2 * eta) * ((1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ u) x‖) +
      (B1 + L) * ((1 + ‖x‖) * ‖fderiv ℝ u x‖) +
      (1 + ‖x‖) * ‖forcingSpaceDeriv G x (u x)‖ := by
  have hp : ‖fderiv ℝ u x‖ ≤ eta := by
    nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ u x))]
  have hw : 0 ≤ 1 + ‖x‖ := by positivity
  have hmain := mul_le_mul_of_nonneg_left (gaugeSource_fderiv_norm_le hb hu hdu hG) hw
  have h1 := mul_le_mul_of_nonneg_right (add_le_add hbb
    (mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num)))
      (mul_nonneg hw (norm_nonneg (fderiv ℝ (fderiv ℝ u) x)))
  have h2 := mul_le_mul_of_nonneg_left hdb
    (mul_nonneg hw (norm_nonneg (fderiv ℝ u x)))
  have h3 := mul_le_mul_of_nonneg_right hGs
    (mul_nonneg hw (norm_nonneg (fderiv ℝ u x)))
  change (1 + ‖x‖) * _ ≤ _ at hmain
  dsimp only [forcingSpaceDeriv, forcingScalarDeriv] at h3 ⊢
  nlinarith



theorem gaugeSource_weighted_fderiv_vanishes_uniformly
    {A : Type*} {b : A → V → V} {G : A → V → ℝ → ℝ} {u : A → V → ℝ}
    {eta B B1 L : ℝ} (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hB1 : 0 ≤ B1) (hL : 0 ≤ L)
    (hbs : ∀ a, ContDiff ℝ ∞ (b a))
    (hGs : ∀ a, ContDiff ℝ ∞ (fun p : V × ℝ => G a p.1 p.2))
    (hus : ∀ a, ContDiff ℝ ∞ (u a))
    (hb : ∀ a x, ‖b a x‖ ≤ B)
    (hdb : ∀ a x, ‖fderiv ℝ (b a) x‖ ≤ B1)
    (hGz : ∀ a x z, (1 + ‖x‖) * |z| ≤ eta → |forcingScalarDeriv (G a) x z| ≤ L)
    (hu : ∀ a x, (1 + ‖x‖) * |u a x| ≤ eta)
    (hdu : ∀ a x, (1 + ‖x‖) * ‖fderiv ℝ (u a) x‖ ≤ eta)
    (hend1 : ∀ e > 0, ∃ R : ℝ, ∀ a x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (u a) x‖ < e)
    (hend2 : ∀ e > 0, ∃ R : ℝ, ∀ a x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (u a)) x‖ < e)
    (hGend : ∀ e > 0, ∃ R : ℝ, ∀ a x z, R ≤ ‖x‖ →
      (1 + ‖x‖) * |z| ≤ eta → (1 + ‖x‖) * ‖forcingSpaceDeriv (G a) x z‖ < e) :
    ∀ e > 0, ∃ R : ℝ, ∀ a x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖fderiv ℝ (gaugeSource (b a) (G a) (u a)) x‖ < e := by
  intro e he
  let K := B + 2 * eta
  let D := B1 + L
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := add_nonneg hB1 hL
  have hd : 0 < K + D + 1 := by positivity
  let d := e / (K + D + 1)
  have hd0 : 0 < d := div_pos he hd
  obtain ⟨R1, hR1⟩ := hend1 d hd0
  obtain ⟨R2, hR2⟩ := hend2 d hd0
  obtain ⟨RG, hRG⟩ := hGend d hd0
  refine ⟨max R1 (max R2 RG), ?_⟩
  intro a x hx
  have h1 := hR1 a x ((le_max_left _ _).trans hx)
  have h2 := hR2 a x ((le_max_left _ _).trans ((le_max_right _ _).trans hx))
  have hg := hRG a x (u a x)
    ((le_max_right _ _).trans ((le_max_right _ _).trans hx)) (hu a x)
  have hs := gaugeSource_weighted_fderiv_tame_bound
    ((hbs a).differentiable (by simp) x) ((hus a).differentiable (by simp) x)
    ((contDiff_infty_iff_fderiv.mp (hus a)).2.differentiable (by simp) x)
    ((hGs a).differentiable (by simp) (x, u a x)) (hb a x) (hdb a x)
    (hdu a x) (hGz a x (u a x) (hu a x))
  have hm1 := mul_le_mul_of_nonneg_left h1.le hD
  have hm2 := mul_le_mul_of_nonneg_left h2.le hK
  have heq : (K + D + 1) * d = e := mul_div_cancel₀ e (ne_of_gt hd)
  change _ ≤ K * _ + D * _ + _ at hs
  nlinarith

end PoincareConjecture.M35.RadialGauge
