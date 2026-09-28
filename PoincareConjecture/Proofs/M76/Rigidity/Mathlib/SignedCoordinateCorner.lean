import PoincareConjecture.Proofs.M76.Mathlib.AffineCornerStraightening









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem exists_signed_coordinate_corner (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∃ F : C3 ≃ₜ C3,
      F.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid C3 ∧ F 0 = 0 ∧
      (∀ y : C3, (0 ≤ y.1.1 ∧ 0 ≤ ε * y.2) ↔ 0 ≤ (F y).1.1) ∧
      (∀ y : C3, (y.1.1 = 0 ∧ 0 ≤ ε * y.2) ↔
        (F y).1.1 = 0 ∧ 0 ≤ ε * (F y).2) ∧
      ∀ y : C3, (y.2 = 0 ∧ 0 ≤ y.1.1) ↔
        (F y).1.1 = 0 ∧ ε * (F y).2 ≤ 0 := by
  let a : C3 →ᴬ[ℝ] ℝ := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap
  let b : C3 →ᴬ[ℝ] ℝ :=
    ε • (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap
  let v : C3 := ((1, 0), 0)
  let w : C3 := ((0, 0), ε)
  have hεsq : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεne : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hav : a.contLinear v = 1 := rfl
  have hbv : b.contLinear v = 0 := by
    change ε * 0 = 0
    exact mul_zero ε
  have haw : a.contLinear w = 0 := rfl
  have hbw : b.contLinear w = 1 := hεsq
  obtain ⟨F, hF, _, _, hfix, hquad, hold, hcap⟩ :=
    a.exists_corner_straightening b v w hav hbv haw hbw
  have hzero : F 0 = 0 := hfix 0 rfl (by
    change ε * 0 = 0
    exact mul_zero ε)
  refine ⟨F, hF, hzero, hquad, hold, ?_⟩
  intro y
  have h := hcap y
  change (ε * y.2 = 0 ∧ 0 ≤ y.1.1) ↔
    (F y).1.1 = 0 ∧ ε * (F y).2 ≤ 0 at h
  simpa only [mul_eq_zero, hεne, false_or] using h

end PoincareConjecture.M76
