import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace PoincareConjecture.RicciFlowAnalysis

private theorem sqrt_quadratic_upper
    (y c : ℝ) (hc : 0 < c) (hy : 0 ≤ y)
    (hδ : |y - c ^ 2| ≤ c ^ 2 / 2) :
    Real.sqrt y ≤ c + (y - c ^ 2) / (2 * c) -
      (y - c ^ 2) ^ 2 / (8 * c ^ 3) + |y - c ^ 2| ^ 3 / c ^ 5 := by
  let δ : ℝ := y - c ^ 2
  let h : ℝ := Real.sqrt y - c
  have hs : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hs2 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have hδeq : δ = h * (Real.sqrt y + c) := by
    dsimp [δ, h]
    nlinarith only [hs2]
  have hδeq' : δ = h * (2 * c + h) := by
    dsimp [δ, h]
    nlinarith only [hs2]
  have hah : |h| ≤ |δ| / c := by
    apply (le_div_iff₀ hc).mpr
    calc
      |h| * c ≤ |h| * (Real.sqrt y + c) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hs) (abs_nonneg h)
      _ = |δ| := by
        rw [hδeq, abs_mul, abs_of_nonneg (add_nonneg hs hc.le)]
  have hahc : |h| ≤ c / 2 := by
    have hbound : |δ| / c ≤ c / 2 := by
      apply (div_le_iff₀ hc).mpr
      change |y - c ^ 2| ≤ c / 2 * c
      nlinarith only [hδ]
    exact hah.trans hbound
  have hfactor : |4 * c + h| ≤ 8 * c := by
    calc
      |4 * c + h| ≤ |4 * c| + |h| := abs_add_le _ _
      _ = 4 * c + |h| := by rw [abs_of_nonneg (by positivity)]
      _ ≤ 8 * c := by linarith
  have hid : h - δ / (2 * c) + δ ^ 2 / (8 * c ^ 3) =
      h ^ 3 * (4 * c + h) / (8 * c ^ 3) := by
    rw [hδeq']
    field_simp [ne_of_gt hc] <;> ring
  have hrem : h ^ 3 * (4 * c + h) / (8 * c ^ 3) ≤ |δ| ^ 3 / c ^ 5 := by
    calc
      h ^ 3 * (4 * c + h) / (8 * c ^ 3) ≤
          |h ^ 3 * (4 * c + h) / (8 * c ^ 3)| := le_abs_self _
      _ = |h| ^ 3 * |4 * c + h| / (8 * c ^ 3) := by
        rw [abs_div, abs_mul, abs_pow,
          abs_of_pos (show 0 < 8 * c ^ 3 by positivity)]
      _ ≤ |h| ^ 3 * (8 * c) / (8 * c ^ 3) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor (by positivity)) (by positivity)
      _ = |h| ^ 3 / c ^ 2 := by
        field_simp [ne_of_gt hc] <;> ring
      _ ≤ (|δ| / c) ^ 3 / c ^ 2 := by
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg h) hah 3) (by positivity)
      _ = |δ| ^ 3 / c ^ 5 := by
        field_simp [ne_of_gt hc] <;> ring
  change Real.sqrt y ≤ c + δ / (2 * c) - δ ^ 2 / (8 * c ^ 3) +
    |δ| ^ 3 / c ^ 5
  have hbound := hid.le.trans hrem
  change Real.sqrt y - c - δ / (2 * c) + δ ^ 2 / (8 * c ^ 3) ≤
    |δ| ^ 3 / c ^ 5 at hbound
  linarith only [hbound]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_sqrt_energy_cubic_majorant_on_ball
    (d L0 Q0 C0 ρ0 : ℝ) (hd : 0 < d)
    (hL0 : 0 ≤ L0) (hQ0 : 0 ≤ Q0) (hC0 : 0 ≤ C0) (hρ0 : 0 < ρ0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ ρ0 ∧ 0 ≤ C ∧
      ∀ (c : ℝ) (E : V → ℝ) (L : V →L[ℝ] ℝ)
        (Q : V →L[ℝ] V →L[ℝ] ℝ),
        d ≤ c → ‖L‖ ≤ L0 → ‖Q‖ ≤ Q0 →
        (∀ z, ‖z‖ < ρ0 →
          |E z - c ^ 2 - L z - Q z z / 2| ≤ C0 * ‖z‖ ^ 3) →
        ∀ z, ‖z‖ < ρ →
          d ^ 2 / 2 ≤ E z ∧
          Real.sqrt (E z) ≤ c + L z / (2 * c) + Q z z / (4 * c) -
            (L z) ^ 2 / (8 * c ^ 3) + C * ‖z‖ ^ 3 := by
  let D0 : ℝ := L0 + Q0 + C0 + 1
  let ρ : ℝ := min ρ0 (min 1 (d ^ 2 / (2 * D0)))
  let C : ℝ := D0 ^ 3 / d ^ 5 + C0 / d + (Q0 + C0) * (D0 + L0) / d ^ 3
  have hD0 : 0 < D0 := by dsimp [D0]; positivity
  have hρ : 0 < ρ := lt_min hρ0 (lt_min zero_lt_one (by positivity))
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρρ0 : ρ ≤ ρ0 := min_le_left _ _
  have hρsq : ρ ≤ d ^ 2 / (2 * D0) := (min_le_right _ _).trans (min_le_right _ _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨ρ, C, hρ, hρ1, hρρ0, hC, ?_⟩
  intro c E L Q hdc hL hQ hE z hz
  let r : ℝ := ‖z‖
  let δ : ℝ := E z - c ^ 2
  have hc : 0 < c := hd.trans_le hdc
  have hr : 0 ≤ r := norm_nonneg z
  have hr1 : r ≤ 1 := hz.le.trans hρ1
  have hz0 : ‖z‖ < ρ0 := hz.trans_le hρρ0
  have hr2 : r ^ 2 ≤ r := by
    nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1)]
  have hr32 : r ^ 3 ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)
    nlinarith only [this]
  have hr3 : r ^ 3 ≤ r := hr32.trans hr2
  have hLz : |L z| ≤ L0 * r := by
    simpa only [Real.norm_eq_abs] using
      (L.le_opNorm z).trans (mul_le_mul_of_nonneg_right hL hr)
  have hQz : |Q z z| ≤ Q0 * r ^ 2 := by
    have h := (Q.le_opNorm₂ z z).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ hr) hr)
    simpa only [Real.norm_eq_abs, r, pow_two, mul_assoc] using h
  have hQhalf : |Q z z / 2| ≤ Q0 * r ^ 2 / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hQz (by norm_num)
  have herr : |δ - L z - Q z z / 2| ≤ C0 * r ^ 3 := hE z hz0
  have hδbound : |δ| ≤ D0 * r := by
    calc
      |δ| = |(δ - L z - Q z z / 2) + L z + Q z z / 2| := by
        congr 1
        ring
      _ ≤ |δ - L z - Q z z / 2| + |L z| + |Q z z / 2| := by
        exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ C0 * r ^ 3 + L0 * r + Q0 * r ^ 2 / 2 := by
        gcongr
      _ ≤ D0 * r := by
        dsimp [D0]
        have hq := mul_le_mul_of_nonneg_left hr2 hQ0
        have he := mul_le_mul_of_nonneg_left hr3 hC0
        nlinarith only [hq, he, hr, mul_nonneg hQ0 hr]
  have hδhalf : |δ| ≤ d ^ 2 / 2 := by
    have hrad : r ≤ d ^ 2 / (2 * D0) := hz.le.trans hρsq
    have hrad' := (le_div_iff₀ (by positivity : 0 < 2 * D0)).mp hrad
    nlinarith only [hδbound, hrad']
  have hdc2 : d ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hd.le hdc 2
  have henergy : d ^ 2 / 2 ≤ E z := by
    have hlow := (abs_le.mp hδhalf).1
    dsimp only [δ] at hlow
    linarith only [hlow, hdc2]
  have henergy0 : 0 ≤ E z := (by positivity : 0 ≤ d ^ 2 / 2).trans henergy
  have hδhalf' : |E z - c ^ 2| ≤ c ^ 2 / 2 := by
    change |δ| ≤ c ^ 2 / 2
    linarith only [hδhalf, hdc2]
  have hsqrt := sqrt_quadratic_upper (E z) c hc henergy0 hδhalf'
  change Real.sqrt (E z) ≤ c + δ / (2 * c) - δ ^ 2 / (8 * c ^ 3) +
    |δ| ^ 3 / c ^ 5 at hsqrt
  have hcubic : |δ| ^ 3 / c ^ 5 ≤ (D0 ^ 3 / d ^ 5) * r ^ 3 := by
    calc
      |δ| ^ 3 / c ^ 5 ≤ (D0 * r) ^ 3 / d ^ 5 :=
        div_le_div₀ (by positivity)
          (pow_le_pow_left₀ (abs_nonneg δ) hδbound 3) (by positivity)
          (pow_le_pow_left₀ hd.le hdc 5)
      _ = (D0 ^ 3 / d ^ 5) * r ^ 3 := by ring
  have hlinear : δ / (2 * c) ≤ L z / (2 * c) + Q z z / (4 * c) +
      (C0 / d) * r ^ 3 := by
    have he := div_le_div_of_nonneg_right ((le_abs_self _).trans herr)
      (by positivity : 0 ≤ 2 * c)
    have hb : C0 * r ^ 3 / (2 * c) ≤ (C0 / d) * r ^ 3 := by
      calc
        C0 * r ^ 3 / (2 * c) ≤ C0 * r ^ 3 / d :=
          div_le_div_of_nonneg_left (by positivity) hd (by linarith)
        _ = (C0 / d) * r ^ 3 := by ring
    have heq : (δ - L z - Q z z / 2) / (2 * c) =
        δ / (2 * c) - L z / (2 * c) - Q z z / (4 * c) := by
      field_simp [ne_of_gt hc] <;> ring
    rw [heq] at he
    linarith only [he, hb]
  have hminus : |δ - L z| ≤ (Q0 + C0) * r ^ 2 := by
    calc
      |δ - L z| = |(δ - L z - Q z z / 2) + Q z z / 2| := by
        congr 1
        ring
      _ ≤ |δ - L z - Q z z / 2| + |Q z z / 2| := abs_add_le _ _
      _ ≤ C0 * r ^ 3 + Q0 * r ^ 2 / 2 := by gcongr
      _ ≤ (Q0 + C0) * r ^ 2 := by
        have he := mul_le_mul_of_nonneg_left hr32 hC0
        nlinarith only [he, mul_nonneg hQ0 (sq_nonneg r)]
  have hplus : |δ + L z| ≤ (D0 + L0) * r := by
    calc
      |δ + L z| ≤ |δ| + |L z| := abs_add_le _ _
      _ ≤ D0 * r + L0 * r := by gcongr
      _ = (D0 + L0) * r := by ring
  have hsquare : |δ ^ 2 - (L z) ^ 2| ≤ (Q0 + C0) * (D0 + L0) * r ^ 3 := by
    calc
      |δ ^ 2 - (L z) ^ 2| = |δ - L z| * |δ + L z| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ ((Q0 + C0) * r ^ 2) * ((D0 + L0) * r) :=
        mul_le_mul hminus hplus (abs_nonneg _) (by positivity)
      _ = (Q0 + C0) * (D0 + L0) * r ^ 3 := by ring
  have hnegative : -(δ ^ 2 / (8 * c ^ 3)) ≤ -((L z) ^ 2 / (8 * c ^ 3)) +
      ((Q0 + C0) * (D0 + L0) / d ^ 3) * r ^ 3 := by
    have hnum : (L z) ^ 2 - δ ^ 2 ≤ (Q0 + C0) * (D0 + L0) * r ^ 3 := by
      apply (le_abs_self _).trans
      simpa only [abs_sub_comm] using hsquare
    have hden : d ^ 3 ≤ 8 * c ^ 3 := by
      have hdc3 := pow_le_pow_left₀ hd.le hdc 3
      nlinarith only [hdc3, pow_nonneg hc.le 3]
    have hfrac := div_le_div₀ (by positivity) hnum (by positivity : 0 < d ^ 3) hden
    rw [sub_div] at hfrac
    have heq : (Q0 + C0) * (D0 + L0) * r ^ 3 / d ^ 3 =
        ((Q0 + C0) * (D0 + L0) / d ^ 3) * r ^ 3 := by ring
    rw [heq] at hfrac
    linarith only [hfrac]
  refine ⟨henergy, ?_⟩
  change Real.sqrt (E z) ≤ c + L z / (2 * c) + Q z z / (4 * c) -
    (L z) ^ 2 / (8 * c ^ 3) + C * r ^ 3
  dsimp only [C]
  linarith only [hsqrt, hcubic, hlinear, hnegative]

theorem exists_sqrt_energy_cubic_majorant
    (d L0 Q0 C0 : ℝ) (hd : 0 < d)
    (hL0 : 0 ≤ L0) (hQ0 : 0 ≤ Q0) (hC0 : 0 ≤ C0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 ≤ C ∧
      ∀ (c : ℝ) (E : V → ℝ) (L : V →L[ℝ] ℝ)
        (Q : V →L[ℝ] V →L[ℝ] ℝ),
        d ≤ c → ‖L‖ ≤ L0 → ‖Q‖ ≤ Q0 →
        (∀ z, ‖z‖ < 1 →
          |E z - c ^ 2 - L z - Q z z / 2| ≤ C0 * ‖z‖ ^ 3) →
        ∀ z, ‖z‖ < ρ →
          d ^ 2 / 2 ≤ E z ∧
          Real.sqrt (E z) ≤ c + L z / (2 * c) + Q z z / (4 * c) -
            (L z) ^ 2 / (8 * c ^ 3) + C * ‖z‖ ^ 3 := by
  obtain ⟨ρ, C, hρ, hρ1, _, hC, hmajorant⟩ :=
    exists_sqrt_energy_cubic_majorant_on_ball (V := V) d L0 Q0 C0 1
      hd hL0 hQ0 hC0 zero_lt_one
  exact ⟨ρ, C, hρ, hρ1, hC, hmajorant⟩

end PoincareConjecture.RicciFlowAnalysis
