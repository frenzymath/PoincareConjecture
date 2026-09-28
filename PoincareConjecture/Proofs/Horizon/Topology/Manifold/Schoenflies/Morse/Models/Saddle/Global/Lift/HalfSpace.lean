import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.Parametric
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_parametric_lift_fixed_below
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ)
    {a b : Real} (hab : a < b) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, H y 2 = y 2) ∧
      (∀ y, y 2 ≤ a → H y = y) ∧
      ∀ y, b ≤ y 2 → H y = toE3 (Φ (χ (y 2)) (y 2) (toE2 y)) (y 2) := by
  let τ : Real → Real := fun z => Real.smoothTransition ((z - a) / (b - a)) * χ z
  have hτ : ContDiff Real ∞ τ :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const (b - a))).mul hχ
  obtain ⟨H, hH, _, hh, _⟩ := exists_height_lift (fun z => Φ (τ z) z)
    (hΦ.comp ((hτ.comp contDiff_fst).prodMk contDiff_id))
    (hΦinv.comp ((hτ.comp contDiff_fst).prodMk contDiff_id))
  refine ⟨H, hh, ?_, ?_⟩
  · intro y hy
    have hτzero : τ (y 2) = 0 := by
      dsimp only [τ]
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) (sub_pos.mpr hab).le), zero_mul]
    rw [hH, hτzero, hzero]
    ext i
    fin_cases i <;> rfl
  · intro y hy
    have hτone : τ (y 2) = χ (y 2) := by
      dsimp only [τ]
      rw [Real.smoothTransition.one_of_one_le
        ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)), one_mul]
    rw [hH, hτone]

theorem exists_parametric_lift_fixed_above
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ)
    {a b : Real} (hab : a < b) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, H y 2 = y 2) ∧
      (∀ y, b ≤ y 2 → H y = y) ∧
      ∀ y, y 2 ≤ a → H y = toE3 (Φ (χ (y 2)) (y 2) (toE2 y)) (y 2) := by
  let τ : Real → Real := fun z => Real.smoothTransition ((b - z) / (b - a)) * χ z
  have hτ : ContDiff Real ∞ τ :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub contDiff_id).div_const (b - a))).mul hχ
  obtain ⟨H, hH, _, hh, _⟩ := exists_height_lift (fun z => Φ (τ z) z)
    (hΦ.comp ((hτ.comp contDiff_fst).prodMk contDiff_id))
    (hΦinv.comp ((hτ.comp contDiff_fst).prodMk contDiff_id))
  refine ⟨H, hh, ?_, ?_⟩
  · intro y hy
    have hτzero : τ (y 2) = 0 := by
      dsimp only [τ]
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) (sub_pos.mpr hab).le), zero_mul]
    rw [hH, hτzero, hzero]
    ext i
    fin_cases i <;> rfl
  · intro y hy
    have hτone : τ (y 2) = χ (y 2) := by
      dsimp only [τ]
      rw [Real.smoothTransition.one_of_one_le
        ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)), one_mul]
    rw [hH, hτone]

end Poincare.Manifold.Schoenflies.Saddle
