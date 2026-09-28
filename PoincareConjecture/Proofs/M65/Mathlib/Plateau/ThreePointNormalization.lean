import PoincareConjecture.Proofs.M65.Mathlib.Plateau.ThreePointPins

set_option autoImplicit false

open scoped ContDiff

namespace Complex

theorem exists_plateau_threePoint_normalization {p q r : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ φ ψ : ℂ → ℂ,
      (∀ z, ‖z‖ ≤ 1 → ‖φ z‖ ≤ 1) ∧
      (∀ z, ‖z‖ ≤ 1 → ‖ψ z‖ ≤ 1) ∧
      (∀ z, ‖z‖ = 1 → ‖φ z‖ = 1) ∧
      (∀ z, ‖z‖ = 1 → ‖ψ z‖ = 1) ∧
      (∀ z, ‖z‖ ≤ 1 → ψ (φ z) = z) ∧
      (∀ z, ‖z‖ ≤ 1 → φ (ψ z) = z) ∧
      (∀ z, ‖z‖ ≤ 1 → ContDiffAt ℂ ∞ φ z) ∧
      (∀ z, ‖z‖ ≤ 1 → ContDiffAt ℂ ∞ ψ z) ∧
      φ p = 1 ∧ φ q = -1 ∧ (φ r = I ∨ φ r = -I) := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hnorm (z : ℂ) : ‖z / p‖ = ‖z‖ := by rw [norm_div, hp, div_one]
  have hq1 : q / p ≠ 1 := by
    intro h
    exact hpq ((div_eq_one_iff_eq hp0).mp h).symm
  have hr1 : r / p ≠ 1 := by
    intro h
    exact hpr ((div_eq_one_iff_eq hp0).mp h).symm
  have hqr' : q / p ≠ r / p := by
    intro h
    exact hqr ((div_left_inj' hp0).mp h)
  obtain ⟨b, c, hc, hfirst, hsecond, hthird⟩ := exists_plateauDiskMap_pins
    ((hnorm q).trans hq) ((hnorm r).trans hr) hq1 hr1 hqr'
  let φ := fun z => plateauDiskMap b c (z / p)
  let ψ := fun z => p * plateauDiskMap (-b / c) (1 / c) z
  have hc' := one_div_pos.mpr hc
  have hscale (z : ℂ) : ‖p * z‖ = ‖z‖ := by rw [norm_mul, hp, one_mul]
  have hback (z : ℂ) (hz : ‖z‖ ≤ 1) :
      plateauDiskMap b c (plateauDiskMap (-b / c) (1 / c) z) = z := by
    have h := plateauDiskMap_left_inverse (-b / c) hc' hz
    have hb : -(-b / c) / (1 / c) = b := by field_simp
    simpa only [hb, one_div_one_div] using h
  refine ⟨φ, ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsecond, hthird⟩
  · intro z hz
    exact plateauDiskMap_norm_le_one b hc ((hnorm z).trans_le hz)
  · intro z hz
    dsimp only [ψ]
    rw [hscale]
    exact plateauDiskMap_norm_le_one (-b / c) hc' hz
  · intro z hz
    exact plateauDiskMap_norm_eq_one b hc ((hnorm z).trans hz)
  · intro z hz
    dsimp only [ψ]
    rw [hscale]
    exact plateauDiskMap_norm_eq_one (-b / c) hc' hz
  · intro z hz
    dsimp only [ψ, φ]
    rw [plateauDiskMap_left_inverse b hc ((hnorm z).trans_le hz), mul_div_cancel₀ _ hp0]
  · intro z hz
    dsimp only [φ, ψ]
    rw [mul_div_cancel_left₀ _ hp0, hback z hz]
  · intro z hz
    dsimp only [φ]
    exact (plateauDiskMap_contDiffAt b hc ((hnorm z).trans_le hz)).comp z
      (show ContDiffAt ℂ ∞ (fun w => w / p) z from by fun_prop)
  · intro z hz
    exact contDiffAt_const.mul (plateauDiskMap_contDiffAt (-b / c) hc' hz)
  · dsimp only [φ]
    rw [div_self hp0, hfirst]

end Complex
