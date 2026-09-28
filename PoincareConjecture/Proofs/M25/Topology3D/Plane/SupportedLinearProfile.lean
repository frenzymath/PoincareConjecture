import PoincareConjecture.Proofs.M25.Topology3D.Plane.ParametricInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv










set_option autoImplicit false

open Set Function MeasureTheory
open scoped ContDiff Manifold Interval

namespace PoincareConjecture.M25.Topology3D



theorem exists_smooth_monotone_clamp :
    ∃ S : ℝ → ℝ, ContDiff ℝ ∞ S ∧
      (∀ y, |y| ≤ 1 → S y = y) ∧
      (∀ y, 2 ≤ y → S y = S 2) ∧
      (∀ y, y ≤ -2 → S y = S (-2)) ∧
      ∀ y, 0 ≤ deriv S y ∧ deriv S y ≤ 1 := by
  let β : ℝ → ℝ := fun y => Real.smoothTransition (2 - y ^ 2)
  have hβ : ContDiff ℝ ∞ β :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))
  have hone (y : ℝ) (hy : |y| ≤ 1) : β y = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have hh := abs_le.mp hy
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (by linarith : 0 ≤ y + 1)]
  have hzero (y : ℝ) (hy : 2 ≤ |y|) : β y = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    nlinarith [sq_abs y, mul_nonneg (sub_nonneg.mpr hy) (by positivity : 0 ≤ |y| + 2)]
  let S : ℝ → ℝ := fun y => ∫ x in (0 : ℝ)..y, β x
  have hd (y : ℝ) : HasDerivAt S (β y) y :=
    (hβ.continuous.integral_hasStrictDerivAt 0 y).hasDerivAt
  have heq : deriv S = β := funext (fun y => (hd y).deriv)
  have hS : ContDiff ℝ ∞ S := contDiff_infty_iff_deriv.mpr
    ⟨fun y => (hd y).differentiableAt, by rw [heq]; exact hβ⟩
  refine ⟨S, hS, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hi : (∫ x in (0 : ℝ)..y, β x) = ∫ _ in (0 : ℝ)..y, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply hone
      exact abs_le.mpr (uIcc_subset_Icc (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)
        (abs_le.mp hy) hx)
    simpa only [S, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hi
  · intro y hy
    have hi : (∫ x in (2 : ℝ)..y, β x) = 0 := by
      calc
        _ = ∫ _ in (2 : ℝ)..y, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hy] at hx
          exact hzero x (hx.1.trans (le_abs_self x))
        _ = 0 := by simp
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (hβ.continuous.intervalIntegrable (μ := volume) 0 2)
      (hβ.continuous.intervalIntegrable (μ := volume) 2 y)
    rw [hi, add_zero] at ha
    exact ha.symm
  · intro y hy
    have hi : (∫ x in (-2 : ℝ)..y, β x) = 0 := by
      calc
        _ = ∫ _ in (-2 : ℝ)..y, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_ge hy] at hx
          exact hzero x (by linarith [neg_le_abs x, hx.2])
        _ = 0 := by simp
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (hβ.continuous.intervalIntegrable (μ := volume) 0 (-2))
      (hβ.continuous.intervalIntegrable (μ := volume) (-2) y)
    rw [hi, add_zero] at ha
    exact ha.symm
  · intro y
    rw [heq]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩



theorem exists_supported_linear_profile {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧
      (∀ y, |y| ≤ 1 → η y = y) ∧
      (∀ y, R ≤ |y| → η y = 0) ∧
      ∀ y, -ε ≤ deriv η y ∧ deriv η y ≤ 1 + ε := by
  obtain ⟨S, hS, hnear, hupper, hlower, hderiv⟩ := exists_smooth_monotone_clamp
  let T := 2 + 1 / ε
  have hT : 2 < T := by dsimp [T]; linarith [one_div_pos.mpr hε]
  have hTpos : 0 < T := by linarith
  have hden : 0 < 1 - 1 / T := by
    have hh : 1 / T < 1 := (div_lt_iff₀ hTpos).mpr (by linarith)
    linarith
  have hsmall : 1 / T ≤ ε * (1 - 1 / T) := by
    have he : T * ε = 2 * ε + 1 := by
      dsimp [T]
      rw [add_mul, one_div_mul_cancel hε.ne']
    apply (div_le_iff₀ hTpos).mpr
    rw [mul_assoc, sub_mul, one_mul, one_div_mul_cancel hTpos.ne']
    nlinarith
  let η : ℝ → ℝ := fun y => (S y - S (y / T)) / (1 - 1 / T)
  have hη : ContDiff ℝ ∞ η :=
    (hS.sub (hS.comp (contDiff_id.div_const T))).div_const _
  have hd (y : ℝ) : HasDerivAt η
      ((deriv S y - deriv S (y / T) / T) / (1 - 1 / T)) y := by
    have hs := (hS.differentiable (by simp) y).hasDerivAt
    have hs' := (hS.differentiable (by simp) (y / T)).hasDerivAt
    convert! (hs.sub (hs'.comp y ((hasDerivAt_id y).div_const T))).div_const
      (1 - 1 / T) using 1
    simp [div_eq_mul_inv]
  refine ⟨2 * T, by positivity, η, hη, ?_, ?_, ?_⟩
  · intro y hy
    have hyT : |y / T| ≤ 1 := by
      rw [abs_div, abs_of_pos hTpos]
      exact (div_le_iff₀ hTpos).mpr (by linarith)
    dsimp only [η]
    rw [hnear y hy, hnear (y / T) hyT]
    apply (div_eq_iff hden.ne').mpr
    ring
  · intro y hy
    dsimp only [η]
    by_cases hy0 : 0 ≤ y
    · rw [abs_of_nonneg hy0] at hy
      rw [hupper y (by linarith),
        hupper (y / T) ((le_div_iff₀ hTpos).mpr (by linarith)), sub_self, zero_div]
    · rw [abs_of_neg (lt_of_not_ge hy0)] at hy
      rw [hlower y (by linarith),
        hlower (y / T) ((div_le_iff₀ hTpos).mpr (by linarith)), sub_self, zero_div]
  · intro y
    rw [(hd y).deriv]
    have hlo : 0 ≤ deriv S (y / T) / T := div_nonneg (hderiv _).1 hTpos.le
    have hhi : deriv S (y / T) / T ≤ 1 / T :=
      div_le_div_of_nonneg_right (hderiv _).2 hTpos.le
    constructor
    · apply (le_div_iff₀ hden).mpr
      nlinarith [(hderiv y).1]
    · apply (div_le_iff₀ hden).mpr
      nlinarith [(hderiv y).2]



theorem exists_supported_positive_scaling
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (c : V → ℝ) (hc : ContDiff ℝ ∞ c) {m M : ℝ} (hm : 0 < m)
    (hbound : ∀ z, m ≤ c z ∧ c z ≤ M) :
    ∃ R : ℝ, 0 < R ∧ ∃ D : (V × ℝ) ≃ₘ[ℝ] (V × ℝ),
      (∀ p, (D p).1 = p.1) ∧
      (∀ z y, |y| ≤ 1 → D (z, y) = (z, c z * y)) ∧
      (∀ z y, R ≤ |y| → D (z, y) = (z, y)) ∧
      (∀ z, c z = 1 → ∀ y, D (z, y) = (z, y)) ∧
      ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧
        ∀ z y, D (z, y) = (z, y + (c z - 1) * η y) := by
  let m0 := min m 1
  let B := max M 1
  let ε := m0 / (2 * (B + 1))
  have hm0 : 0 < m0 := lt_min hm zero_lt_one
  have hB : 1 ≤ B := le_max_right _ _
  have hε : 0 < ε := div_pos hm0 (by positivity)
  have hεB : ε * (B + 1) = m0 / 2 := by
    dsimp only [ε]
    field_simp
  have hsmall (z : V) : ε * |c z - 1| < min 1 (c z) := by
    have hcb : c z ≤ B := (hbound z).2.trans (le_max_left _ _)
    have hcz : 0 < c z := hm.trans_le (hbound z).1
    have habs : |c z - 1| ≤ B + 1 := by rw [abs_le]; constructor <;> linarith
    have hh := mul_le_mul_of_nonneg_left habs hε.le
    rw [hεB] at hh
    exact lt_of_le_of_lt hh (lt_of_lt_of_le (half_lt_self hm0)
      (le_min (min_le_right m 1) ((min_le_left m 1).trans (hbound z).1)))
  obtain ⟨R, hR, η, hη, hnear, hzero, hηderiv⟩ := exists_supported_linear_profile hε
  let f : V × ℝ → ℝ := fun p => p.2 + (c p.1 - 1) * η p.2
  have hf : ContDiff ℝ ∞ f := contDiff_snd.add
    (((hc.comp contDiff_fst).sub contDiff_const).mul (hη.comp contDiff_snd))
  have hd (z : V) (y : ℝ) : HasDerivAt (fun s => f (z, s))
      (1 + (c z - 1) * deriv η y) y :=
    (hasDerivAt_id y).add
      (((hη.differentiable (by simp) y).hasDerivAt).const_mul (c z - 1))
  have hpos (z : V) (y : ℝ) : 0 < deriv (fun s => f (z, s)) y := by
    rw [(hd z y).deriv]
    by_cases hz : 1 ≤ c z
    · have hh := (hsmall z).trans_le (min_le_left _ _)
      rw [abs_of_nonneg (sub_nonneg.mpr hz)] at hh
      have hmul := mul_le_mul_of_nonneg_left (hηderiv y).1 (sub_nonneg.mpr hz)
      nlinarith
    · have hz' : c z ≤ 1 := (lt_of_not_ge hz).le
      have hh := (hsmall z).trans_le (min_le_right _ _)
      rw [abs_of_nonpos (sub_nonpos.mpr hz')] at hh
      have hmul := mul_le_mul_of_nonpos_left (hηderiv y).2 (sub_nonpos.mpr hz')
      nlinarith
  have htail (z : V) (y : ℝ) (hy : y ≤ -R ∨ R ≤ y) : f (z, y) = y := by
    have hyR : R ≤ |y| := by
      rcases hy with hy | hy
      · linarith [neg_le_abs y]
      · exact hy.trans (le_abs_self y)
    simp only [f, hzero y hyR, mul_zero, add_zero]
  have hsurj (z : V) : Surjective (fun y => f (z, y)) :=
    surjective_of_eq_self_outside_interval
      (hf.continuous.comp (continuous_const.prodMk continuous_id)) (-R) R (htail z)
  let D := fiberDiffeomorph hf hpos hsurj
  have hformula (z : V) (y : ℝ) : D (z, y) = (z, y + (c z - 1) * η y) := rfl
  refine ⟨R, hR, D, (fun _ => rfl), ?_, ?_, ?_, η, hη, hformula⟩
  · intro z y hy
    rw [hformula, hnear y hy]
    congr 1
    ring
  · intro z y hy
    rw [hformula, hzero y hy, mul_zero, add_zero]
  · intro z hz y
    rw [hformula, hz, sub_self, zero_mul, add_zero]

end PoincareConjecture.M25.Topology3D
